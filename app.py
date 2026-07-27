import io
import os
import re
import shutil
import zipfile
import tempfile
import webbrowser
import time
from copy import deepcopy
from functools import lru_cache
from pathlib import Path
from threading import Timer

from lxml import etree as ET

from flask import Flask, render_template, request, jsonify, send_file
from werkzeug.utils import secure_filename
from werkzeug.exceptions import RequestEntityTooLarge

BASE_DIR = Path(__file__).resolve().parent
MAPPINGS_DIR = BASE_DIR / "mappings"
OUTPUT_DIR = BASE_DIR / "output_docs"
OUTPUT_DIR.mkdir(exist_ok=True)

# Directory to store user uploaded files
UPLOADS_DIR = BASE_DIR / "uploads"
UPLOADS_DIR.mkdir(exist_ok=True)

W_NS = "http://schemas.openxmlformats.org/wordprocessingml/2006/main"
R_NS = "http://schemas.openxmlformats.org/officeDocument/2006/relationships"
XML_NS = "http://www.w3.org/XML/1998/namespace"

NS = {"w": W_NS, "r": R_NS}
XML_PART_EXCLUDE_PREFIXES = ("theme/", "_rels/", "customXml/")
TAMIL_RE = re.compile(r"[\u0B80-\u0BFF]")


DEFAULT_FONT_CONFIG = {
    "unicode": {
        "doc_font": "Arial Unicode MS",
        "aliases": [
            "arial unicode ms",
            "latha",
            "vijaya",
            "nirmala ui",
            "nirmalaui",
            "tau-marutham",
            "marutham"
        ]
    },
    "bamini": {
        "doc_font": "Bamini",
        "aliases": ["bamini"]
    },
    "vanavil": {
        "doc_font": "VANAVIL-Avvaiyar",
        "aliases": ["vanavil-avvaiyar", "vanavil avvaiyar", "vanavil"]
    },
    "sathayam": {
        "doc_font": "Sathayam",
        "aliases": ["sathayam"]
    },
    "anankuhelv": {
        "doc_font": "Ananku Helv",
        "aliases": ["ananku helv", "anankuhelv"]
    },
    "divya": {
        "doc_font": "divya",
        "aliases": ["divya"]
    }
}

XML_PARSER = ET.XMLParser(
    remove_blank_text=False,
    resolve_entities=False,
    recover=False,
    strip_cdata=False,
    ns_clean=False,
    huge_tree=True
)

app = Flask(__name__)
app.config["MAX_CONTENT_LENGTH"] = 100 * 1024 * 1024


def norm(s):
    return re.sub(r"[_\-\s]+", "", (s or "").strip().lower())


def parse_js_string(src, start):
    q = src[start]
    i = start + 1
    out = []
    n = len(src)
    escapes = {
        "n": "\n", "r": "\r", "t": "\t", "b": "\b", "f": "\f",
        '"': '"', "'": "'", "\\": "\\", "/": "/"
    }

    while i < n:
        ch = src[i]
        if ch == "\\":
            i += 1
            if i >= n:
                break
            esc = src[i]
            if esc == "u" and i + 4 < n:
                hex_part = src[i + 1:i + 5]
                try:
                    out.append(chr(int(hex_part, 16)))
                    i += 5
                    continue
                except ValueError:
                    out.append("u")
                    i += 1
                    continue
            out.append(escapes.get(esc, esc))
            i += 1
            continue
        if ch == q:
            return "".join(out), i + 1
        out.append(ch)
        i += 1

    raise ValueError("Unterminated JS string")


def parse_js_mapping(path):
    src = Path(path).read_text(encoding="utf-8")
    m = re.search(r"const\s+([A-Za-z0-9_]+)\s*=\s*\{", src)
    if not m:
        raise ValueError(f"Invalid mapping file: {path.name}")

    i = src.find("{", m.end() - 1) + 1
    n = len(src)
    data = {}

    while i < n:
        while i < n and src[i] in " \t\r\n,":
            i += 1
        if i >= n or src[i] == "}":
            break

        if src[i:i + 2] == "//":
            i = src.find("\n", i)
            if i == -1:
                break
            continue

        if src[i] not in ('"', "'"):
            i += 1
            continue

        key, i = parse_js_string(src, i)

        while i < n and src[i] in " \t\r\n":
            i += 1
        if i < n and src[i] == ":":
            i += 1
        while i < n and src[i] in " \t\r\n":
            i += 1

        if i >= n or src[i] not in ('"', "'"):
            raise ValueError(f"Invalid value in {path.name}")

        value, i = parse_js_string(src, i)
        data[key] = value

        while i < n and src[i] not in ",}":
            i += 1
        if i < n and src[i] == ",":
            i += 1

    return data


def create_pattern(mapping):
    keys = sorted((k for k in mapping.keys() if k), key=len, reverse=True)
    escaped_keys = [re.escape(k) for k in keys]
    return re.compile("|".join(escaped_keys)) if escaped_keys else re.compile(r"(?!x)x")


def convert_text_regex(text, mapping, pattern):
    if not text or not mapping:
        return text
    return pattern.sub(lambda m: mapping[m.group(0)], text)


def build_match_index(mapping):
    keys = sorted(mapping.keys(), key=len, reverse=True)
    by_first = {}
    for k in keys:
        if not k:
            continue
        by_first.setdefault(k[0], []).append(k)
    return {
        "keys": keys,
        "by_first": by_first
    }


def convert_text_longest_first(text, mapping, match_index=None):
    if not text or not mapping:
        return text

    if match_index is None:
        match_index = build_match_index(mapping)

    by_first = match_index["by_first"]
    out = []
    i = 0
    n = len(text)

    while i < n:
        candidates = by_first.get(text[i], [])
        matched = None

        for key in candidates:
            if text.startswith(key, i):
                matched = key
                break

        if matched is not None:
            out.append(mapping[matched])
            i += len(matched)
        else:
            out.append(text[i])
            i += 1

    return "".join(out)


def better_parse(a, b):
    if a["raw"] != b["raw"]:
        return a["raw"] < b["raw"]
    if a["converted_chars"] != b["converted_chars"]:
        return a["converted_chars"] > b["converted_chars"]
    if a["tokens"] != b["tokens"]:
        return a["tokens"] < b["tokens"]
    if a["first_key_len"] != b["first_key_len"]:
        return a["first_key_len"] > b["first_key_len"]
    return False


def convert_text_best_parse(text, mapping, match_index=None):
    if not text or not mapping:
        return text

    if match_index is None:
        match_index = build_match_index(mapping)

    by_first = match_index["by_first"]
    n = len(text)
    dp = [None] * (n + 1)
    dp[n] = {
        "raw": 0,
        "converted_chars": 0,
        "tokens": 0,
        "first_key_len": 0,
        "next_i": None,
        "piece": "",
    }

    for i in range(n - 1, -1, -1):
        best = None

        for key in by_first.get(text[i], []):
            if text.startswith(key, i):
                rest = dp[i + len(key)]
                cand = {
                    "raw": rest["raw"],
                    "converted_chars": rest["converted_chars"] + len(key),
                    "tokens": rest["tokens"] + 1,
                    "first_key_len": len(key),
                    "next_i": i + len(key),
                    "piece": mapping[key],
                }
                if best is None or better_parse(cand, best):
                    best = cand

        rest = dp[i + 1]
        raw_cand = {
            "raw": rest["raw"] + 1,
            "converted_chars": rest["converted_chars"],
            "tokens": rest["tokens"] + 1,
            "first_key_len": 0,
            "next_i": i + 1,
            "piece": text[i],
        }

        if best is None or better_parse(raw_cand, best):
            best = raw_cand

        dp[i] = best

    out = []
    i = 0
    while i < n:
        state = dp[i]
        out.append(state["piece"])
        i = state["next_i"]

    return "".join(out)

def reverse_mapping_first_wins(mapping):
    rev = {}
    for k, v in mapping.items():
        if v not in rev:
            rev[v] = k
    return rev


def compose_mappings(map1, map2):
    pattern2 = create_pattern(map2)
    out = {}
    for k, v in map1.items():
        out[k] = convert_text_regex(v, map2, pattern2)
    return out


def safe_filename_part(s):
    s = re.sub(r"[^A-Za-z0-9._-]+", "_", (s or "").strip())
    return s.strip("._") or "file"


class TamilDocxConverter:
    def __init__(self, font_config=None):
        self.font_config = deepcopy(font_config or DEFAULT_FONT_CONFIG)
        self.mappings = {}
        self.mapping_errors = []
        self.base_unicode_maps = {}
        self.doc_defaults_font = None
        self.style_run_fonts = {}
        self.style_based_on = {}
        self.refresh()

    def register_mapping(self, src, dst, mapping, file_label, kind):
        self.mappings[(src.lower(), dst.lower())] = {
            "map": mapping,
            "pattern": create_pattern(mapping),
            "match_index": build_match_index(mapping),
            "file": file_label,
            "kind": kind
        }

    def refresh(self):
        self.mappings = {}
        self.mapping_errors = []
        self.base_unicode_maps = {}
        self.doc_defaults_font = None
        self.style_run_fonts = {}
        self.style_based_on = {}

        for js_file in sorted(MAPPINGS_DIR.glob("*.js")):
            stem = js_file.stem.lower()
            if not stem.endswith("_to_unicode"):
                continue

            src = stem[:-len("_to_unicode")]

            try:
                mapping = parse_js_mapping(js_file)
                self.base_unicode_maps[src] = {
                    "map": mapping,
                    "file": js_file.name
                }
            except Exception as e:
                self.mapping_errors.append({
                    "file": js_file.name,
                    "error": str(e)
                })

        self.build_all_mappings()

    def build_all_mappings(self):
        available = dict(self.base_unicode_maps)
        ids = sorted(available.keys())

        for font_id in ids:
            base_map = available[font_id]["map"]
            base_file = available[font_id]["file"]

            self.register_mapping(
                font_id,
                "unicode",
                base_map,
                base_file,
                "base"
            )

            self.register_mapping(
                "unicode",
                font_id,
                reverse_mapping_first_wins(base_map),
                f"[auto-reverse] {base_file}",
                "auto-reverse"
            )

        for src in ids:
            for dst in ids:
                if src == dst:
                    continue
                src_to_unicode = self.get_mapping_entry(src, "unicode")
                unicode_to_dst = self.get_mapping_entry("unicode", dst)
                if not src_to_unicode or not unicode_to_dst:
                    continue
                composed = compose_mappings(src_to_unicode["map"], unicode_to_dst["map"])
                self.register_mapping(
                    src,
                    dst,
                    composed,
                    f"[auto-compose] {src_to_unicode['file']} + {unicode_to_dst['file']}",
                    "auto-compose"
                )

    def known_encodings(self):
        names = {"unicode"}
        names.update(self.font_config.keys())
        names.update(self.base_unicode_maps.keys())
        names.update(a for a, _ in self.mappings.keys())
        names.update(b for _, b in self.mappings.keys())
        return sorted(names)

    def doc_font_for_encoding(self, encoding):
        cfg = self.font_config.get(encoding.lower(), {})
        return cfg.get("doc_font") or encoding

    def doc_font_aliases(self, encoding):
        cfg = self.font_config.get(encoding.lower(), {})
        vals = [cfg.get("doc_font", "")]
        vals.extend(cfg.get("aliases", []))
        return {norm(v) for v in vals if v}

    def font_matches_encoding(self, font_name, encoding):
        if not font_name:
            return False
        return norm(font_name) in self.doc_font_aliases(encoding)

    def prefers_best_parse(self, source_encoding):
        return source_encoding.lower() != "unicode"

    def get_mapping_entry(self, src, dst):
        return self.mappings.get((src.lower(), dst.lower()))

    def build_pipeline(self, source_encoding, target_encoding):
        s = source_encoding.lower()
        t = target_encoding.lower()

        if s == t:
            raise ValueError("Source and target must be different")

        if s != "unicode" and t != "unicode":
            s_to_unicode = self.get_mapping_entry(s, "unicode")
            unicode_to_t = self.get_mapping_entry("unicode", t)
            if s_to_unicode and unicode_to_t:
                return [
                    (s, "unicode", s_to_unicode),
                    ("unicode", t, unicode_to_t)
                ]

        direct = self.get_mapping_entry(s, t)
        if direct:
            return [(s, t, direct)]

        raise ValueError(f"No mapping path found: {source_encoding} -> {target_encoding}")

    def get_font_name(self, rpr):
        if rpr is None:
            return None
        rfonts = rpr.find(f"{{{W_NS}}}rFonts")
        if rfonts is None:
            return None
        for attr in ("ascii", "hAnsi", "cs", "eastAsia"):
            val = rfonts.get(f"{{{W_NS}}}{attr}")
            if val:
                return val
        return None

    def get_rfonts_name(self, elem):
        if elem is None:
            return None
        for attr in ("ascii", "hAnsi", "cs", "eastAsia"):
            val = elem.get(f"{{{W_NS}}}{attr}")
            if val:
                return val
        return None

    def load_styles_from_root(self, temp_root):
        self.doc_defaults_font = None
        self.style_run_fonts = {}
        self.style_based_on = {}

        styles_path = Path(temp_root) / "word" / "styles.xml"
        if not styles_path.exists():
            return

        try:
            tree = ET.parse(styles_path)
            root = tree.getroot()
        except ET.ParseError:
            return

        doc_defaults_rfonts = root.find(".//w:docDefaults/w:rPrDefault/w:rPr/w:rFonts", NS)
        self.doc_defaults_font = self.get_rfonts_name(doc_defaults_rfonts)

        for st in root.findall(".//w:style", NS):
            style_id = st.get(f"{{{W_NS}}}styleId")
            if not style_id:
                continue

            based_on = st.find("w:basedOn", NS)
            if based_on is not None:
                val = based_on.get(f"{{{W_NS}}}val")
                if val:
                    self.style_based_on[style_id] = val

            rfonts = st.find("w:rPr/w:rFonts", NS)
            font_name = self.get_rfonts_name(rfonts)
            if font_name:
                self.style_run_fonts[style_id] = font_name

    def resolve_style_font(self, style_id, seen=None):
        if not style_id:
            return None
        if seen is None:
            seen = set()
        if style_id in seen:
            return None
        seen.add(style_id)

        if style_id in self.style_run_fonts:
            return self.style_run_fonts[style_id]

        parent = self.style_based_on.get(style_id)
        if parent:
            return self.resolve_style_font(parent, seen)

        return None

    def get_paragraph_style_id(self, para):
        ppr = para.find("w:pPr", NS)
        if ppr is None:
            return None
        pstyle = ppr.find("w:pStyle", NS)
        if pstyle is None:
            return None
        return pstyle.get(f"{{{W_NS}}}val")

    def get_effective_font_name(self, run, para=None):
        rpr = run.find("w:rPr", NS)
        font_name = self.get_font_name(rpr)
        if font_name:
            return font_name

        if para is not None:
            rrstyle = rpr.find("w:rStyle", NS) if rpr is not None else None
            if rrstyle is not None:
                style_id = rrstyle.get(f"{{{W_NS}}}val")
                style_font = self.resolve_style_font(style_id)
                if style_font:
                    return style_font

            style_id = self.get_paragraph_style_id(para)
            style_font = self.resolve_style_font(style_id)
            if style_font:
                return style_font

        return self.doc_defaults_font

    def set_font(self, rpr, font_name, legacy_mode=False):
        if rpr is None:
            return

        rfonts = rpr.find(f"{{{W_NS}}}rFonts")
        if rfonts is None:
            rfonts = ET.SubElement(rpr, f"{{{W_NS}}}rFonts")

        for attr in ("asciiTheme", "hAnsiTheme", "cstheme", "csTheme", "eastAsiaTheme"):
            qn = f"{{{W_NS}}}{attr}"
            if qn in rfonts.attrib:
                del rfonts.attrib[qn]

        rfonts.set(f"{{{W_NS}}}ascii", font_name)
        rfonts.set(f"{{{W_NS}}}hAnsi", font_name)

        if legacy_mode:
            for attr in ("cs", "eastAsia"):
                qn = f"{{{W_NS}}}{attr}"
                if qn in rfonts.attrib:
                    del rfonts.attrib[qn]
        else:
            rfonts.set(f"{{{W_NS}}}cs", font_name)
            rfonts.set(f"{{{W_NS}}}eastAsia", font_name)

    def remove_font_assignments(self, rpr):
        if rpr is None:
            return

        rfonts = rpr.find(f"{{{W_NS}}}rFonts")
        if rfonts is None:
            return

        for attr in (
            "ascii", "hAnsi", "cs", "eastAsia",
            "asciiTheme", "hAnsiTheme", "cstheme", "csTheme", "eastAsiaTheme"
        ):
            qn = f"{{{W_NS}}}{attr}"
            if qn in rfonts.attrib:
                del rfonts.attrib[qn]

        if not rfonts.attrib:
            rpr.remove(rfonts)

    def cleanup_rpr_for_legacy(self, rpr):
        if rpr is None:
            return

        self.remove_font_assignments(rpr)

        remove_tags = {
            f"{{{W_NS}}}rtl",
            f"{{{W_NS}}}cs",
            f"{{{W_NS}}}lang",
            f"{{{W_NS}}}eastAsianLayout",
            f"{{{W_NS}}}specVanish",
            f"{{{W_NS}}}webHidden",
        }

        for child in list(rpr):
            if child.tag in remove_tags:
                rpr.remove(child)

    def normalize_run_for_target(self, run, target_encoding, font_name=None):
        rpr = run.find(f"{{{W_NS}}}rPr")
        if rpr is None:
            rpr = ET.Element(f"{{{W_NS}}}rPr")
            run.insert(0, rpr)

        if target_encoding.lower() == "unicode":
            if font_name:
                self.set_font(rpr, font_name, legacy_mode=False)
        else:
            self.cleanup_rpr_for_legacy(rpr)
            if font_name:
                self.set_font(rpr, font_name, legacy_mode=True)

    def get_font_size_vals(self, rpr):
        if rpr is None:
            return (None, None)
        sz = rpr.find(f"{{{W_NS}}}sz")
        szcs = rpr.find(f"{{{W_NS}}}szCs")
        sz_val = sz.get(f"{{{W_NS}}}val") if sz is not None else None
        szcs_val = szcs.get(f"{{{W_NS}}}val") if szcs is not None else None
        return sz_val, szcs_val

    def set_font_size_vals(self, rpr, sz_val=None, szcs_val=None):
        if rpr is None:
            return

        if sz_val:
            sz = rpr.find(f"{{{W_NS}}}sz")
            if sz is None:
                sz = ET.SubElement(rpr, f"{{{W_NS}}}sz")
            sz.set(f"{{{W_NS}}}val", str(sz_val))

        if szcs_val:
            szcs = rpr.find(f"{{{W_NS}}}szCs")
            if szcs is None:
                szcs = ET.SubElement(rpr, f"{{{W_NS}}}szCs")
            szcs.set(f"{{{W_NS}}}val", str(szcs_val))

    def preserve_space(self, t_elem, text):
        if text and (text[:1].isspace() or text[-1:].isspace() or " " in text):
            t_elem.set(f"{{{XML_NS}}}space", "preserve")
        else:
            t_elem.attrib.pop(f"{{{XML_NS}}}space", None)

    def clone_run_props_only(self, run):
        new_run = ET.Element(f"{{{W_NS}}}r")
        rpr = run.find(f"{{{W_NS}}}rPr")
        if rpr is not None:
            new_run.append(deepcopy(rpr))
        return new_run

    def make_text_run_from_template(self, template_run, text, font_name=None, target_encoding=None):
        new_run = self.clone_run_props_only(template_run)

        rpr = new_run.find(f"{{{W_NS}}}rPr")
        if rpr is None:
            rpr = ET.Element(f"{{{W_NS}}}rPr")
            new_run.insert(0, rpr)

        if target_encoding:
            self.normalize_run_for_target(new_run, target_encoding, font_name)
        elif font_name:
            self.set_font(rpr, font_name)

        t = ET.Element(f"{{{W_NS}}}t")
        t.text = text
        self.preserve_space(t, text)
        new_run.append(t)
        return new_run

    def make_tab_run_from_template(self, template_run):
        new_run = self.clone_run_props_only(template_run)
        tab = ET.Element(f"{{{W_NS}}}tab")
        new_run.append(tab)
        return new_run

    def run_props_signature(self, run):
        rpr = run.find(f"{{{W_NS}}}rPr")
        if rpr is None:
            return ""
        return ET.tostring(rpr, encoding="unicode")

    def merge_adjacent_runs(self, runs):
        if not runs:
            return []

        merged = []
        current = deepcopy(runs[0])

        for nxt in runs[1:]:
            current_text_elem = None
            next_text_elem = None

            current_non_rpr = [c.tag for c in list(current) if c.tag != f"{{{W_NS}}}rPr"]
            next_non_rpr = [c.tag for c in list(nxt) if c.tag != f"{{{W_NS}}}rPr"]

            if current_non_rpr == [f"{{{W_NS}}}t"] and next_non_rpr == [f"{{{W_NS}}}t"]:
                current_text_elem = current.find(f"{{{W_NS}}}t")
                next_text_elem = nxt.find(f"{{{W_NS}}}t")

            if (
                current_text_elem is not None and
                next_text_elem is not None and
                self.run_props_signature(current) == self.run_props_signature(nxt)
            ):
                current_text_elem.text = (current_text_elem.text or "") + (next_text_elem.text or "")
                self.preserve_space(current_text_elem, current_text_elem.text or "")
            else:
                merged.append(current)
                current = deepcopy(nxt)

        merged.append(current)
        return merged

    def tokenize_run(self, run):
        tokens = []
        for child in list(run):
            if child.tag == f"{{{W_NS}}}rPr":
                continue
            if child.tag == f"{{{W_NS}}}t":
                text = child.text or ""
                if text:
                    tokens.append({"type": "text", "text": text, "run": run})
            elif child.tag == f"{{{W_NS}}}tab":
                tokens.append({"type": "tab", "run": run})
            elif child.tag == f"{{{W_NS}}}br":
                tokens.append({"type": "break", "run": run, "elem": deepcopy(child)})
            else:
                tokens.append({"type": "xml", "run": run, "elem": deepcopy(child)})
        return tokens

    def collect_paragraph_tokens(self, para):
        tokens = []
        runs = []
        for child in list(para):
            if child.tag != f"{{{W_NS}}}r":
                continue
            run_tokens = self.tokenize_run(child)
            if run_tokens:
                runs.append(child)
                tokens.extend(run_tokens)
        return runs, tokens

    def collect_runs_with_flags(self, para, source_encoding):
        runs = []
        for child in list(para):
            if child.tag != f"{{{W_NS}}}r":
                continue
            effective_font = self.get_effective_font_name(child, para)
            runs.append({
                "run": child,
                "font": effective_font,
                "convertible": self.font_matches_encoding(effective_font, source_encoding),
                "tokens": self.tokenize_run(child)
            })
        return runs

    def choose_template_run_for_group(self, run_infos, source_encoding):
        best_run = None
        best_score = None

        for info in run_infos:
            run = info["run"]
            rpr = run.find("w:rPr", NS)
            font_name = info.get("font") or self.get_effective_font_name(run)
            sz_val, szcs_val = self.get_font_size_vals(rpr)

            text_len = 0
            for tok in info["tokens"]:
                if tok["type"] == "text":
                    text_len += len(tok["text"])

            score = (
                1 if self.font_matches_encoding(font_name, source_encoding) else 0,
                text_len,
                int(szcs_val or sz_val or 0)
            )

            if best_score is None or score > best_score:
                best_score = score
                best_run = run

        return best_run or run_infos[0]["run"]

    def split_unicode_segments(self, text, mapping):
        if not text:
            return []

        def kind(ch):
            if TAMIL_RE.search(ch):
                return "convertible"
            if ch == " ":
                return "convertible"
            if ch in mapping:
                return "convertible"
            return "other"

        segments = []
        buf = [text[0]]
        current_kind = kind(text[0])

        for ch in text[1:]:
            k = kind(ch)
            if k == current_kind:
                buf.append(ch)
            else:
                segments.append((current_kind, "".join(buf)))
                buf = [ch]
                current_kind = k

        segments.append((current_kind, "".join(buf)))
        return segments

    def convert_unicode_text_preserving_other(self, text, mapping_entry):
        mapping = mapping_entry["map"]
        pattern = mapping_entry["pattern"]
        segments = self.split_unicode_segments(text, mapping)

        converted_parts = []
        changed_chars = 0

        for kind, seg_text in segments:
            if kind == "convertible":
                converted = convert_text_regex(seg_text, mapping, pattern)
                if converted != seg_text:
                    changed_chars += len(seg_text)
                converted_parts.append(("converted", converted))
            else:
                converted_parts.append(("other", seg_text))

        return converted_parts, changed_chars

    def replace_paragraph_runs(self, para, original_runs, new_runs):
        if not original_runs:
            return False

        parent_children = list(para)
        insert_at = None
        for idx, child in enumerate(parent_children):
            if child is original_runs[0]:
                insert_at = idx
                break

        if insert_at is None:
            return False

        for r in original_runs:
            if r in list(para):
                para.remove(r)

        for nr in reversed(new_runs):
            para.insert(insert_at, nr)

        return True

    def build_preserved_runs_from_original(self, run_infos):
        new_runs = []

        for info in run_infos:
            run = info["run"]
            for tok in info["tokens"]:
                if tok["type"] == "text":
                    new_runs.append(self.make_text_run_from_template(run, tok["text"], None))
                elif tok["type"] == "tab":
                    new_runs.append(self.make_tab_run_from_template(run))
                elif tok["type"] == "break":
                    nr = self.clone_run_props_only(run)
                    nr.append(tok["elem"])
                    new_runs.append(nr)
                elif tok["type"] == "xml":
                    nr = self.clone_run_props_only(run)
                    nr.append(tok["elem"])
                    new_runs.append(nr)

        return new_runs

    def convert_legacy_text_to_unicode(self, text, mapping_entry, source_encoding):
        if self.prefers_best_parse(source_encoding):
            return convert_text_best_parse(
                text,
                mapping_entry["map"],
                mapping_entry.get("match_index")
            )
        return convert_text_longest_first(
            text,
            mapping_entry["map"],
            mapping_entry.get("match_index")
        )

    def convert_via_pipeline_text(self, text, pipeline, source_encoding, target_encoding):
        current = text

        if len(pipeline) == 1:
            s, t, entry = pipeline[0]
            if s != "unicode" and t == "unicode":
                current = self.convert_legacy_text_to_unicode(current, entry, source_encoding)
            elif s == "unicode" and t != "unicode":
                current = convert_text_regex(current, entry["map"], entry["pattern"])
            else:
                current = convert_text_regex(current, entry["map"], entry["pattern"])
            return current

        for s, t, entry in pipeline:
            if s != "unicode" and t == "unicode":
                current = self.convert_legacy_text_to_unicode(current, entry, s)
            elif s == "unicode" and t != "unicode":
                current = convert_text_regex(current, entry["map"], entry["pattern"])
            else:
                current = convert_text_regex(current, entry["map"], entry["pattern"])

        return current

    def build_converted_runs_for_group(
        self, run_infos, pipeline, source_encoding, target_encoding
    ):
        full_text_parts = []
        template_run = self.choose_template_run_for_group(run_infos, source_encoding)

        for info in run_infos:
            for tok in info["tokens"]:
                if tok["type"] == "text":
                    full_text_parts.append(tok["text"])
                elif tok["type"] == "tab":
                    full_text_parts.append("\t")

        if template_run is None:
            return [], 0, 0

        full_text = "".join(full_text_parts)
        converted = self.convert_via_pipeline_text(
            full_text,
            pipeline,
            source_encoding,
            target_encoding
        )

        same_text = (converted == full_text)
        legacy_to_legacy = (
            source_encoding.lower() != "unicode" and
            target_encoding.lower() != "unicode"
        )

        if same_text and not legacy_to_legacy:
            return self.build_preserved_runs_from_original(run_infos), 0, 0

        target_doc_font = self.doc_font_for_encoding(target_encoding)
        new_runs = []
        current_text = []

        template_rpr = template_run.find("w:rPr", NS)
        t_sz, t_szcs = self.get_font_size_vals(template_rpr)

        def flush_text():
            nonlocal current_text
            if current_text:
                text_out = "".join(current_text)
                new_run = self.make_text_run_from_template(
                    template_run,
                    text_out,
                    target_doc_font,
                    target_encoding=target_encoding
                )
                rpr = new_run.find(f"{{{W_NS}}}rPr")
                if rpr is None:
                    rpr = ET.Element(f"{{{W_NS}}}rPr")
                    new_run.insert(0, rpr)
                self.set_font(rpr, target_doc_font, legacy_mode=(target_encoding.lower() != "unicode"))
                self.set_font_size_vals(rpr, t_sz, t_szcs or t_sz)
                new_runs.append(new_run)
                current_text = []

        for ch in converted:
            if ch == "\t":
                flush_text()
                tab_run = self.make_tab_run_from_template(template_run)
                tab_rpr = tab_run.find(f"{{{W_NS}}}rPr")
                if tab_rpr is None:
                    tab_rpr = ET.Element(f"{{{W_NS}}}rPr")
                    tab_run.insert(0, tab_rpr)
                if target_encoding.lower() != "unicode":
                    self.normalize_run_for_target(tab_run, target_encoding, target_doc_font)
                else:
                    self.set_font(tab_rpr, target_doc_font, legacy_mode=False)
                self.set_font_size_vals(tab_rpr, t_sz, t_szcs or t_sz)
                new_runs.append(tab_run)
            else:
                current_text.append(ch)

        flush_text()
        processed_chars = len(full_text) if (not same_text or legacy_to_legacy) else 0
        processed_runs = len(run_infos) if (not same_text or legacy_to_legacy) else 0
        return new_runs, processed_chars, processed_runs

    def looks_like_legacy_payload(self, text):
        if not text:
            return False
        tamil_chars = sum(1 for ch in text if "\u0B80" <= ch <= "\u0BFF")
        ascii_letters = sum(1 for ch in text if ("A" <= ch <= "Z") or ("a" <= ch <= "z"))
        return tamil_chars == 0 and ascii_letters > 0

    def convert_paragraph_legacy_runs(
        self, para, source_encoding, target_encoding, pipeline
    ):
        run_infos = self.collect_runs_with_flags(para, source_encoding)
        original_runs = [x["run"] for x in run_infos if x["tokens"]]

        if not original_runs:
            return 0, 0, 0

        convertible_count = sum(1 for x in run_infos if x["convertible"])
        if convertible_count == 0:
            para_text = "".join(
                tok["text"]
                for info in run_infos
                for tok in info["tokens"]
                if tok["type"] == "text"
            )
            if self.looks_like_legacy_payload(para_text):
                for info in run_infos:
                    if info["tokens"]:
                        info["convertible"] = True

        grouped = []
        current_group = []
        current_flag = None

        for info in run_infos:
            if not info["tokens"]:
                continue
            flag = info["convertible"]
            if current_group and flag != current_flag:
                grouped.append((current_flag, current_group))
                current_group = [info]
                current_flag = flag
            else:
                if not current_group:
                    current_flag = flag
                current_group.append(info)

        if current_group:
            grouped.append((current_flag, current_group))

        new_runs = []
        changed_chars = 0
        changed_runs = 0

        for is_convertible, group in grouped:
            if is_convertible:
                converted_runs, local_changed, local_runs = self.build_converted_runs_for_group(
                    group, pipeline, source_encoding, target_encoding
                )
                changed_chars += local_changed
                changed_runs += local_runs
                new_runs.extend(converted_runs)
            else:
                new_runs.extend(self.build_preserved_runs_from_original(group))

        if changed_chars == 0:
            return 0, 0, 0

        ok = self.replace_paragraph_runs(para, original_runs, new_runs)
        if not ok:
            return 0, 0, 0

        return 1, changed_chars, changed_runs

    def convert_paragraph(self, para, source_encoding, target_encoding, pipeline):
        if source_encoding.lower() != "unicode":
            return self.convert_paragraph_legacy_runs(
                para, source_encoding, target_encoding, pipeline
            )

        original_runs, tokens = self.collect_paragraph_tokens(para)
        if not original_runs or not tokens:
            return 0, 0, 0

        new_runs = []
        changed_chars = 0
        changed_runs = 0
        paragraph_changed = False

        source_doc_font = self.doc_font_for_encoding(source_encoding)
        target_doc_font = self.doc_font_for_encoding(target_encoding)
        unicode_fallback_font = self.doc_font_for_encoding("unicode")
        is_unicode_to_legacy = target_encoding.lower() != "unicode"

        for tok in tokens:
            template_run = tok["run"]
            rpr = template_run.find("w:rPr", NS)
            original_font = self.get_font_name(rpr)

            if tok["type"] == "text":
                text = tok["text"]
                parts, changed = self.convert_unicode_text_preserving_other(text, pipeline[0][2])
                changed_chars += changed

                for part_kind, part_text in parts:
                    if not part_text:
                        continue

                    if part_kind == "converted":
                        current = part_text
                        font_name = target_doc_font
                        out_target_encoding = target_encoding
                    else:
                        current = part_text
                        out_target_encoding = "unicode"
                        if original_font and not self.font_matches_encoding(original_font, target_encoding):
                            font_name = original_font
                        else:
                            font_name = unicode_fallback_font or source_doc_font

                    new_runs.append(
                        self.make_text_run_from_template(
                            template_run,
                            current,
                            font_name=font_name,
                            target_encoding=out_target_encoding
                        )
                    )

                if changed:
                    paragraph_changed = True
                    changed_runs += 1

            elif tok["type"] == "tab":
                new_run = self.make_tab_run_from_template(template_run)
                if is_unicode_to_legacy:
                    self.normalize_run_for_target(new_run, target_encoding, target_doc_font)
                new_runs.append(new_run)

            elif tok["type"] == "break":
                new_run = self.clone_run_props_only(template_run)
                if is_unicode_to_legacy:
                    self.normalize_run_for_target(new_run, target_encoding, target_doc_font)
                new_run.append(tok["elem"])
                new_runs.append(new_run)

            elif tok["type"] == "xml":
                new_run = self.clone_run_props_only(template_run)
                if is_unicode_to_legacy:
                    self.normalize_run_for_target(new_run, target_encoding, target_doc_font)
                new_run.append(tok["elem"])
                new_runs.append(new_run)

        if not paragraph_changed:
            return 0, 0, 0

        if is_unicode_to_legacy:
            new_runs = self.merge_adjacent_runs(new_runs)

        ok = self.replace_paragraph_runs(para, original_runs, new_runs)
        if not ok:
            return 0, 0, 0

        return 1, changed_chars, changed_runs

    def story_parts(self, temp_root):
        word = Path(temp_root) / "word"
        parts = []
        if not word.exists():
            return parts

        for path in sorted(word.rglob("*.xml")):
            rel = path.relative_to(word).as_posix()
            if any(rel.startswith(p) for p in XML_PART_EXCLUDE_PREFIXES):
                continue
            parts.append(path)

        return parts

    def parse_xml_file(self, xml_path):
        return ET.parse(str(xml_path), XML_PARSER)

    def write_xml_file(self, tree, xml_path):
        tree.write(
            str(xml_path),
            encoding="UTF-8",
            xml_declaration=True,
            standalone=None,
            pretty_print=False
        )

    def convert_xml_tree(self, tree, source_encoding, target_encoding):
        pipeline = self.build_pipeline(source_encoding, target_encoding)

        converted_paragraphs = 0
        converted_chars = 0
        converted_runs = 0

        for para in tree.findall(".//w:p", NS):
            p_count, c_count, r_count = self.convert_paragraph(
                para,
                source_encoding=source_encoding,
                target_encoding=target_encoding,
                pipeline=pipeline
            )
            converted_paragraphs += p_count
            converted_chars += c_count
            converted_runs += r_count

        return converted_paragraphs, converted_chars, converted_runs

    def convert_docx(self, file_storage, source_encoding, target_encoding):
        self.refresh()
        pipeline = self.build_pipeline(source_encoding, target_encoding)

        temp_root = tempfile.mkdtemp(prefix="tamil_docx_")
        input_name = Path(file_storage.filename or "document.docx").name
        src_tag = safe_filename_part(source_encoding)
        dst_tag = safe_filename_part(target_encoding)
        output_name = f"{Path(input_name).stem}_{src_tag}_to_{dst_tag}.docx"
        
        # Read uploaded file bytes
        file_storage.seek(0)
        input_bytes = file_storage.read()

        try:
            with zipfile.ZipFile(io.BytesIO(input_bytes), "r") as zf:
                zf.extractall(temp_root)

            self.load_styles_from_root(temp_root)

            total_paragraphs = 0
            total_chars = 0
            total_runs = 0

            for xml_path in self.story_parts(temp_root):
                try:
                    tree = ET.parse(xml_path)
                except ET.ParseError:
                    continue

                paragraphs, chars, runs = self.convert_xml_tree(tree, source_encoding, target_encoding)
                if paragraphs or chars or runs:
                    self.write_xml_file(tree, xml_path)

                total_paragraphs += paragraphs
                total_chars += chars
                total_runs += runs

            out_path = OUTPUT_DIR / output_name
            with zipfile.ZipFile(out_path, "w", zipfile.ZIP_DEFLATED) as zf:
                for folder, _, files in os.walk(temp_root):
                    for fname in files:
                        full = Path(folder) / fname
                        zf.write(full, full.relative_to(temp_root).as_posix())

            return out_path, total_paragraphs, total_chars, total_runs, pipeline

        finally:
            shutil.rmtree(temp_root, ignore_errors=True)


converter = TamilDocxConverter()


@app.errorhandler(RequestEntityTooLarge)
def handle_large_file(_e):
    return jsonify({
        "ok": False,
        "error": "File too large. Maximum allowed size is 100 MB."
    }), 413


@app.get("/")
def home():
    converter.refresh()
    fonts = converter.known_encodings()

    pairs = sorted(
        [
            {
                "source": s,
                "target": t,
                "count": len(v["map"]),
                "file": v["file"],
                "kind": v["kind"],
                "source_doc_font": converter.doc_font_for_encoding(s),
                "target_doc_font": converter.doc_font_for_encoding(t)
            }
            for (s, t), v in converter.mappings.items()
            if s != t
        ],
        key=lambda x: (x["source"], x["target"])
    )

    encodings = [
        {
            "name": e,
            "doc_font": converter.doc_font_for_encoding(e),
            "aliases": sorted(converter.doc_font_aliases(e))
        }
        for e in fonts
    ]

    return render_template(
        "index.html",
        fonts=fonts,
        encodings=encodings,
        pairs=pairs,
        mapping_count=len(pairs),
        total_directional_pairs=len(pairs),
        font_config=converter.font_config,
        mapping_errors=converter.mapping_errors
    )


@app.get("/api/debug/mappings")
def debug_mappings():
    converter.refresh()
    return jsonify({
        "ok": True,
        "base_unicode_maps": [
            {
                "encoding": k,
                "file": v["file"],
                "count": len(v["map"])
            }
            for k, v in sorted(converter.base_unicode_maps.items())
        ],
        "known_encodings": converter.known_encodings(),
        "pair_count": len([1 for (s, t) in converter.mappings.keys() if s != t]),
        "pairs": [
            {
                "source": s,
                "target": t,
                "file": v["file"],
                "kind": v["kind"],
                "count": len(v["map"])
            }
            for (s, t), v in sorted(converter.mappings.items())
            if s != t
        ],
        "errors": converter.mapping_errors
    })


@app.get("/api/files")
def list_files():
    """Lists uploaded files and converted output files."""
    def get_file_info(directory, route_prefix):
        files = []
        for path in sorted(directory.glob("*.docx"), key=os.path.getmtime, reverse=True):
            stat = path.stat()
            files.append({
                "filename": path.name,
                "size_kb": round(stat.st_size / 1024, 2),
                "modified": time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(stat.st_mtime)),
                "download_url": f"/{route_prefix}/{path.name}"
            })
        return files

    return jsonify({
        "ok": True,
        "uploads": get_file_info(UPLOADS_DIR, "download/upload"),
        "converted": get_file_info(OUTPUT_DIR, "download/converted")
    })


@app.post("/api/convert")
def convert_api():
    file = request.files.get("docx")
    source_font = (request.form.get("source_font") or "").strip().lower()
    target_font = (request.form.get("target_font") or "").strip().lower()

    if not file or not file.filename.lower().endswith(".docx"):
        return jsonify({"ok": False, "error": "Choose a valid .docx file"}), 400
    if not source_font or not target_font:
        return jsonify({"ok": False, "error": "Choose source and target fonts"}), 400
    if source_font == target_font:
        return jsonify({"ok": False, "error": "Source and target must be different"}), 400

    try:
        # Save the raw uploaded file with a timestamp to avoid overwrite collisions
        timestamp = int(time.time())
        clean_name = secure_filename(file.filename) or "document.docx"
        saved_upload_path = UPLOADS_DIR / f"{timestamp}_{clean_name}"
        file.save(saved_upload_path)

        # Process conversion
        out_path, paragraphs, chars, runs, pipeline = converter.convert_docx(file, source_font, target_font)

        return jsonify({
            "ok": True,
            "filename": out_path.name,
            "uploaded_as": saved_upload_path.name,
            "paragraphs": paragraphs,
            "chars": chars,
            "runs": runs,
            "download": f"/download/converted/{out_path.name}",
            "upload_download": f"/download/upload/{saved_upload_path.name}",
            "pipeline": [
                {"source": s, "target": t, "file": m["file"], "kind": m["kind"]}
                for s, t, m in pipeline
            ],
            "source_doc_font": converter.doc_font_for_encoding(source_font),
            "target_doc_font": converter.doc_font_for_encoding(target_font)
        })
    except Exception as e:
        return jsonify({"ok": False, "error": str(e)}), 500


@app.get("/download/<filename>")
@app.get("/download/converted/<filename>")
def download_converted(filename):
    return send_file(OUTPUT_DIR / filename, as_attachment=True, download_name=filename)


@app.get("/download/upload/<filename>")
def download_upload(filename):
    return send_file(UPLOADS_DIR / filename, as_attachment=True, download_name=filename)


def open_browser():
    webbrowser.open("http://127.0.0.1:5000")


if __name__ == "__main__":
    print("\nTamil DOCX Font Converter")
    print(f"Folder: {BASE_DIR}")
    print(f"Mappings: {MAPPINGS_DIR}")
    print("Open: http://127.0.0.1:5000")
    print("Mode: build mappings from *_to_unicode.js, convert legacy↔unicode and legacy↔legacy via Unicode pivot")
    print("Debug mappings: http://127.0.0.1:5000/api/debug/mappings")
    print("View all files: http://127.0.0.1:5000/api/files\n")
    Timer(1.2, open_browser).start()
    app.run(host="0.0.0.0", port=5000, debug=False)
