# PDF Cite Analyzer
Replaces the internal links in a paper pdf with NASA ADS links. Will require some changes from paper to paper, so recommended familiarity with python.

## Requirements
* [pdfminer](https://github.com/pdfminer/pdfminer.six); [pypi](https://pypi.org/project/pdfminer.six/)
* [pdfrw](https://github.com/pmaupin/pdfrw); [pypi](https://pypi.org/project/pdfrw/)
* [astroquery](https://astroquery.readthedocs.io/en/latest/)
* [tzlocal](https://github.com/regebro/tzlocal); [pypi](https://pypi.org/project/tzlocal/)
* [anystyle command line tool](https://anystyle.io/)

## Usage
`python pdf_cite_analyzer.py <input file> <output file>`

## Notes
There is a step which requires a file called `replace_rules.txt` to be in the top level directory. This file helps with cleaning up scraped text from the PDF so that the name and year attached to the inline citation can be adequately parsed even when the scraped text is garbled. The format of this file is:
```
<input> -> <replace>
<input 2> -> <replace 2>
;;;
<input> -> <replace>
<input 2> -> <replace 2>
 ```
 Before the `;;;` are replacements done before the regrex attempts to parse the inline citation whereas after the `;;;` are replacements done on each group the regrex finds. The specific regrex is `([A-Za-z0-9.\- ]+)(?:[.+ ]+|&.+)\(?(\d{4}[ab]?)` where group 1 is the first authors name and group 2 is the year.
