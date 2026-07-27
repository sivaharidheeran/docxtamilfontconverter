Tamil DOCX Font Converter

Files and folders:
- app.py
- templates\index.html
- mappings\*.js
- output_docs\
- requirements.txt

How to use:
1. Put your .js mapping files inside mappings folder.
2. Put your font files inside fonts folder if you want to keep them together.
3. Install Python 3 if not already installed.
4. Install Flask once: pip install -r requirements.txt
5. Double-click run_converter.bat
6. Browser opens automatically.
7. Choose DOCX, source font, and target font.
8. Convert and download output DOCX.

Notes:
- Unicode output font is forced to Arial Unicode MS.
- English-font runs are left untouched.
- Existing run formatting like bold, italic, underline, and color is preserved.
- Main story parts, tables, headers, footers, footnotes, endnotes, and comments are processed.