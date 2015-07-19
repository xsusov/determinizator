# determinizator

Transforms finite automaton's formal specificationto it's determinized form.

Requires: python 3

Usage:

optional arguments:

  -h, --help            	show this help message and exit

  --input INPUT         	input file with formal specification of finite automaton.Default: STDIN

  --output OUTPUT       	output file for savingformal specification of determinized finite automaton.Default: STDOUT

  -i, --case-insensitive	Symbols and states are treated case insensitive.

  -r, --rules-only		Works with shortened input finite automaton specificationcontaining only rule.

  -w, --white-char      	Tokens in file with finite automaton doesn't have to be separated by comma.

  -e, --no-epsilon-rules	Mode: removes epsilon transition functions in FA.

  -d, --determinization		Mode: determinization of FA.

  --analyze-string STRING	Mode: string analyzation.Verifies if finite automaton accepts given string.

  --wsfa			Mode: Well specified finite automaton. Result WSFA is finite automaton has no epsilon transitionfunctions


---
Tomáš Sušovský 2015 tomas.susovsky@gmail.com

