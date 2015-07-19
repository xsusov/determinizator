#!/usr/bin/env python3.2.3
# -*- coding: utf-8 -*-
## @package determinizator
#   DETERMINIZATOR
#   Determinizace konecneho automatu
#
#   Program for transformation formal specification of finite automatons.
#   Loads FA specification from file or standard input and produce new FA
#   specification with (depending on arguments given by user):
#       - removed epsilon-transition functions (rules)
#       - determinization applied

#   imports
import argparse
import sys

__author__ = 'Tomáš Sušovský'
__email__ = 'tomas.susovsky@gmail.com'
# CONSTANTS:
ENCODING = 'UTF-8'
# return values constants:
GUTT = 0
ARGUMENT_ERROR = 1
INPUT_ERROR = 2
OUTPUT_ERROR = 3
FORMAT_ERROR = 40
SEMANTIC_ERROR = 41
UNKNOWN_SYMBOL = 1
# error messages:
ERR_ARGUMENT = 'ERROR INVALID ARGUMENT'
ERR_MISSING_ARGUMENT = 'ERROR PROGRAMS ARGUMENTS MISSING, SEE: --help'
ERR_OPENING_IN = 'ERROR OPENING INPUT FILE'
ERR_CLOSING_IN = 'ERROR CLOSING INPUT FILE'
ERR_OPENING_OUT = 'ERROR OPENING OUTPUT FILE'
ERR_INPUT_FILE_FORMAT = 'ERROR INPUT FILE FORMAT'
ERR_RULE_SEMANTIC = 'ERROR UNKNOWN STATES OR SYMBOL USED IN RULE'
ERR_START_STATE = 'ERROR UNKNOWN STATE USED AS START STATE'
ERR_ACCEPT_STATE = 'ERROR UNKNOWN STATE USED IN SET OF ACCEPT STATES'
ERR_EMPTY_ALPHABET = 'ERROR ALPHABET EMPTY'
ERR_UNKNOWN_SYMBOL = 'ERROR SYMBOL USED IN STRING NOT IN ALPHABET'
# arguments help messages:
DKA_HELP_DESC = 'Transforms finite automaton\'s formal specification'\
                'to it\'s determinized form.'
HELP_DETERMINIZATION = 'Mode: determinization of FA.'
HELP_NO_EPSILON_RULES = 'Mode: removes epsilon transition functions in FA.'
HELP_CASE_INSENSITIVE = 'Symbols and states are treated case insensitive.'
HELP_OUTPUT = 'output file for saving' \
              'formal specification of determinized finite automaton.'\
              'Default: STDOUT'
HELP_INPUT = 'input file with formal specification of finite automaton.'\
             'Default: STDIN'
HELP_ANALYZE_STRING = 'Mode: string analyzation.'\
                      'Verifies if finite automaton accepts given string.'
HELP_RULES_ONLY = 'Works with shortened input finite automaton specification'\
                  'containing only rule.'
HELP_WSFA = 'Mode: Well specified finite automaton. ' \
            'Result WSFA is finite automaton has no epsilon transition' \
            'functions'
HELP_WHITE_CHAR = 'Tokens in file with finite automaton ' \
                  'doesn\'t have to be separated by comma.'
# format special characters
CHAR_FA_BEGIN = '('
CHAR_FA_END = ')'
CHAR_COMMENT = '#'
CHAR_OPEN = '{'
CHAR_CLOSED = '}'
CHAR_SEPARATOR = ','
CHAR_EOF = ''
CHAR_EOT = '\x04'
CHAR_APOSTROPHE = '\''
CHAR_UNDERSCORE = '_'
EPSILON = "''"
# special strings
SET_JOIN = ', '
RULE_ARROW = ' -> '
STRING_ACCEPTED = '1'
STRING_NOT_ACCEPTED = '0'
# trap states:
TRAP = 'qFALSE'


##
# @class FiniteAutomaton
# @brief class for storing representation of finite automaton
#   constructor creates empty FA and load method can adds elements
#   to it's atributes. Other methods provide transformation
#   to specific kind of finite automatons
class FiniteAutomaton():

    ##
    # @brief static method for joining multiple states
    #   (sorted in  lexicographical order)m underscore is used as default
    #   for joining states.
    # @return final joined state
    @classmethod
    def join_set(cls, set_to_join=set(), joint=SET_JOIN):
        return joint.join(sorted(list(set_to_join)))

    ##
    # @brief constructor, that creates empty FA
    def __init__(self):
        self.states = set()
        self.alphabet = set()
        self.rules = set()
        self.start = ''
        self.accept = set()

    ##
    # @brief method that loads FA by its components.
    #   Checks if there isn't any bad character after FA,
    #   except white chars and comments
    # @param file - FileReade used to read components from
    #   (standard input as default)
    # @param rules_only - in case of rules only mode calls other
    #   method for loading FA
    def load(self, file=sys.stdin, rules_only=False):
        if rules_only:
            return self.load_rules_only_automaton(file)
        # get begin of automaton:
        file.read_char(CHAR_FA_BEGIN)
        # states:
        file.read_open()
        self.load_states_from_file(file)
        file.read_char(CHAR_SEPARATOR)
        # alphabet:
        file.read_open()
        self.load_alphabet_from_file(file)
        file.read_char(CHAR_SEPARATOR)
        # rules:
        file.read_open()
        self.load_rules_from_file(file)
        file.read_char(CHAR_SEPARATOR)
        # start state:
        self.load_start(file)
        file.read_separator()
        # accept states:
        file.read_open()
        self.load_accept(file)
        # get end of automaton:
        file.read_char(CHAR_FA_END)
        # read rest of file (only whitespaces or comments are allowed)
        file.read_char(CHAR_EOF)
        self.sort()
        file.close()

    ##
    # @brief sorts FA components in lexicographical order
    def sort(self):
        self.states = sorted(self.states)
        self.alphabet = sorted(self.alphabet)
        self.rules = sorted(self.rules)
        self.accept = sorted(self.accept)

    ##
    # @brief loads one state and adds it to FA state atribute
    # @param file - FileReader to read from (default standard input)
    # @return loaded state
    def load_rules_only_state(self, file=sys.stdin):
        state = file.read_state()
        self.add_state(state)
        return state

    ##
    # @brief method used to load FA in rules-only mode
    # @param file - FileReader to read from (default standard input)
    def load_rules_only_automaton(self, file=sys.stdin):
        while True:
            state_from = self.load_rules_only_state(file)
            if self.start == '':
                self.start = state_from
            symbol = file.read_symbol(True)
            self.add_symbol(symbol)
            file.read_char('-')
            file.read()
            if not file.is_char('>'):
                sys.stderr.write(ERR_INPUT_FILE_FORMAT)
                exit(FORMAT_ERROR)
            state_to = self.load_rules_only_state(file)
            if file.is_char('.'):
                self.add_accept(state_to)
                file.read()
            self.add_rule(state_from, symbol, state_to)
            file.filter_whitespace()
            # check for last rule
            if not file.is_char(CHAR_SEPARATOR):
                break

        # check if there isn't anything else than FA specification in file
        if not file.is_char(CHAR_EOF):
            exit(FORMAT_ERROR)
        file.close()
        self.sort()
        return True

    ##
    # @brief adds state to set of states, prevents duplicates
    # @param state - state to add
    def add_state(self, state):
        self.states |= {state}

    ##
    # @brief adds symbol to FA's alphabet of accepted symbols
    #   checks that epsilon cannot be in FA alphabet
    # @param symbol - symbol to be added
    def add_symbol(self, symbol):
        if symbol == EPSILON:
            exit(FORMAT_ERROR)
        self.alphabet |= {symbol}

    ##
    # @brief adds new rule to FA's set of rules
    #   checks if all parts of rule are in corresponding atributes of FA
    # @param state_form - initial state
    # @param symbol - alphabet symbol of this transition function
    # @param state_to - final state of rule
    def add_rule(self, state_from, symbol, state_to):
        if not(state_from in self.states and state_to in self.states
               and (symbol in self.alphabet or symbol == EPSILON)):
            sys.stderr.write(ERR_RULE_SEMANTIC)
            exit(SEMANTIC_ERROR)
        self.rules.add((state_from, symbol, state_to))

    ##
    # @brief sets start state of FA on state
    #   checks if start state is in set of FA's states
    # @param state to be start state
    def set_start(self, state):
        if state not in self.states:
            sys.stderr.write(ERR_START_STATE)
            exit(SEMANTIC_ERROR)
        self.start = state

    ##
    # @brief adds accept state of FA
    #   checks if accept state is in set of FA's states
    # @param state to be accept state
    def add_accept(self, state):
        if state not in self.states:
            sys.stderr.write(ERR_ACCEPT_STATE)
            exit(SEMANTIC_ERROR)
        self.accept |= {state}

    def load_states_from_file(self, file):
        while not file.is_char(CHAR_CLOSED):
            state = file.read_state()
            self.add_state(state)
            file.read_separator()

    ##
    # @brief loads all alphabet symbols from file
    #   checks if FA's alphabet is not empty.
    # @param file - FileReader to read from (default standard input)
    def load_alphabet_from_file(self, file):
        while not file.is_char(CHAR_CLOSED):
            symbol = file.read_symbol()
            if symbol == '' and file.is_char(CHAR_CLOSED):
                break
            self.add_symbol(symbol)
            file.read(1)
            file.read_separator()
        if len(self.alphabet) == 0:
            sys.stderr.write(ERR_EMPTY_ALPHABET)
            exit(SEMANTIC_ERROR)

    ##
    # @brief loads all rules from file
    # @param file - FileReader to read from (default standard input)
    def load_rules_from_file(self, file):
        while not file.is_char(CHAR_CLOSED):
            state_from = file.read_state()
            # empty set of rules
            if file.is_char(CHAR_CLOSED) and state_from == '':
                file.read_separator()
                break
            symbol = file.read_symbol(True)
            file.read_char('-')
            file.read()
            if not file.is_char('>'):
                sys.stderr.write(ERR_INPUT_FILE_FORMAT)
                exit(FORMAT_ERROR)
            state_to = file.read_state()
            self.add_rule(state_from, symbol, state_to)
            file.read_separator()

    ##
    # @brief loads FA's start state from file
    # @param file - FileReader to read from (default standard input)
    def load_start(self, file):
        self.set_start(file.read_state())

    ##
    # @brief loads FA's accept states from file
    # @param file - FileReader to read from (default standard input)
    def load_accept(self, file):
        while not(file.is_char(CHAR_CLOSED)):
            accept_state = file.read_state()
            if file.is_char(CHAR_CLOSED)\
                    and (accept_state == '' or accept_state == CHAR_CLOSED):
                file.read_separator()
                break
            self.add_accept(accept_state)
            file.read_separator()

    ##
    # @brief writes FA to output file (standard output as default)
    #   by all components and separated by given characters.
    def print(self, file=sys.stdout):
        file.write(CHAR_FA_BEGIN + '\n'
                   + CHAR_OPEN + self.join_set(self.states) + CHAR_CLOSED
                   + CHAR_SEPARATOR + '\n'
                   + CHAR_OPEN + SET_JOIN.join(self.alphabet) + CHAR_CLOSED
                   + CHAR_SEPARATOR + '\n'
                   + CHAR_OPEN + '\n')

        i = 0
        for rule in self.rules:
            file.write(rule[0] + ' ' + rule[1] + RULE_ARROW + rule[2])
            i += 1
            if i < len(self.rules):
                file.write(CHAR_SEPARATOR)
            file.write('\n')

        file.write(CHAR_CLOSED + CHAR_SEPARATOR + '\n'
                   + self.start + CHAR_SEPARATOR + '\n'
                   + CHAR_OPEN + SET_JOIN.join(self.accept)
                   + CHAR_CLOSED + '\n'
                   + CHAR_FA_END)

    ##
    # @brief finds all epsilon closures of given state
    # @param state state for it it's closures found
    # @return set of state's closures
    def epsilon_closure(self, state):
        closure_i = set()
        closure_i.add(state)
        closure_i_last = set()
        while closure_i != closure_i_last:
            closure_i_last |= closure_i
            for rule in self.rules:
                if rule[0] in closure_i_last and rule[1] == EPSILON:
                    closure_i.add(rule[2])
        return sorted(closure_i)

    ##
    # @brief removes all epsilon rules from FA.
    #   Original rules and accept states are replaced by new sets of rules
    #   and accept states excluding epsilon rules
    def remove_epsilon_rules(self):
        no_epsilon_rules = set()
        no_epsilon_accept = set()
        for state in self.states:
            state_closures = self.epsilon_closure(state)
            for closure in state_closures:
                for rule in self.rules:
                    if rule[0] == closure and rule[1] != EPSILON:
                        no_epsilon_rules.add((state, rule[1], rule[2]))
                if closure in self.accept:
                    no_epsilon_accept.add(state)

        self.rules = sorted(no_epsilon_rules)
        self.accept = sorted(no_epsilon_accept)

    ##
    # @brief determinizes FA
    #   creates new set where are determinized components added,
    #   After determinization old sets are replaced by determinizated ones.
    def determinize(self):
        determinizated_states = set()
        determinizated_rules = set()
        determinizated_start = self.start
        determizated_accept = set()

        new_states = set()
        new_states.add(determinizated_start)

        while len(new_states) > 0:
            new_state_from = new_states.pop()
            determinizated_states.add(new_state_from)
            for symbol in self.alphabet:
                new_states_to = set()
                for rule in self.rules:
                    if rule[0] in new_state_from and rule[1] == symbol:
                        new_states_to.add(rule[2])
                if len(new_states_to) > 0:
                    joined_state = self.join_set(new_states_to,
                                                 CHAR_UNDERSCORE)
                    determinizated_rules.add((new_state_from,
                                              symbol, joined_state))
                    if joined_state not in determinizated_states:
                        new_states.add(joined_state)
                        if len(new_states_to.intersection(self.accept)) > 0:
                            determizated_accept.add(joined_state)

            if new_state_from in self.accept:
                determizated_accept.add(new_state_from)

        self.states = sorted(determinizated_states)
        self.rules = sorted(determinizated_rules)
        self.start = determinizated_start
        self.accept = sorted(determizated_accept)

    ##
    # @brief removes all unacceptable state from FA
    def remove_unacceptable_states(self):
        acceptable_states = set()
        acceptable_states |= set(self.accept)
        last_acceptable_states = set()
        while acceptable_states != last_acceptable_states:
            last_acceptable_states |= acceptable_states
            for state in last_acceptable_states:
                for rule in self.rules:
                    if rule[2] == state:
                        acceptable_states.add(rule[0])

        acceptable_rules = set()
        for rule in self.rules:
            if rule[0] in acceptable_states and rule[2] in acceptable_states:
                acceptable_rules.add(rule)

        self.states = acceptable_states
        self.rules = acceptable_rules

    ##
    # @brief transforms determinizated FA to well specified FA
    # @param case_insensitive - default False
    # - dependence for creating name of trap state
    def transform_to_complete(self, case_insensitive=False):
        trap = TRAP if not case_insensitive else TRAP.lower()
        self.states.add(trap)
        if self.start not in self.states:
            self.start = trap

        for state in self.states:
            for symbol in self.alphabet:
                if self.get_next_state(state, symbol) == CHAR_EOF:
                    self.rules.add((state, symbol, trap))
        self.sort()

    ##
    # @brief gets final state from rules for initial state and symbol
    # @param state_from - initial state
    # @param symbol - rule's symbol
    # @return final state or empty string if none is found
    def get_next_state(self, state_from, symbol):
        for rule in self.rules:
            if rule[0] == state_from and rule[1] == symbol:
                return rule[2]
        return CHAR_EOF

    ##
    # @brief method for analyzing string against FA.
    # @param string - string given by user to be analyzed
    def analyze_string(self, string):
        state = self.start
        escape = ''
        for char in string:
            if char == CHAR_APOSTROPHE:
                char += CHAR_APOSTROPHE
            if char == '\\':
                escape = '\\'
                continue
            symbol = "'" + escape + char + "'"
            if symbol not in self.alphabet:
                sys.stderr.write(ERR_UNKNOWN_SYMBOL)
                exit(UNKNOWN_SYMBOL)
            state = self.get_next_state(state, symbol)
            if state == CHAR_EOF:
                return False
            escape = ''
        return state in self.accept


##
#   @class FileReader
#   @brief wrapper class for reading from file
#       with memory of last char and current string in it's atributes
class FileReader():

    ##
    # CONSTRUCTOR
    # @brief opens input file (default standard input)
    #   and sets atributes to empty state
    # @param input_file - file used for reading
    # @param case_mode - parameter for case-insensitive mode support
    def __init__(self, input_file=sys.stdin, case_mode=False):
        self.file = sys.stdin
        if input_file is not None:
            try:
                self.file = open(input_file, "r", encoding=ENCODING)
            except IOError:
                sys.stderr.write(ERR_OPENING_IN)
                exit(INPUT_ERROR)
        self.char = ''
        self.str = ''
        self.case_insensitive = case_mode

    ##
    # DESTRUCTOR
    # @brief Destructor - closes input file
    def __del__(self):
        self.file.close()

    ##
    # @brief closes input file
    #   handles possible exceptions
    def close(self):
        try:
            self.file.close()
        except IOError:
            sys.stderr.write(ERR_CLOSING_IN)
            exit(INPUT_ERROR)

    ##
    # @brief appends current character to string atribute
    def append_char(self):
        self.str += str(self.char)

    ##
    # @brief reads single char from input file.
    #   If case-insensitive mode is applied, ale read characters are
    #   transformed to it's lower form.
    # @return read character
    def read(self, length=1):
        self.char = self.file.read(length)
        if self.case_insensitive:
            self.char = self.char.lower()
        return self.char

    ##
    # @brief filters comment (comment to end of line) from input
    # @return True if any comment was filtered
    def filter_comment(self):
        if self.is_comment():
            while self.char not in ['\n', '\r', '']:
                self.read()
            self.read()
            self.filter_comment()
            return True
        else:
            return False

    ##
    # @brief filters all whitespaces and comments on input
    def filter_whitespace(self):
        self.filter_comment()
        while self.is_whitespace():
            self.read()
            self.filter_comment()

    ##
    # @brief reads single char from input file,
    #   it's assigned to char atribute of FileReader
    # @param target_char - used as block if file was read to end
    def read_char(self, target_char=CHAR_EOF):
        if self.is_char(target_char):
            return self.char
        self.read()
        self.filter_whitespace()
        if not(self.is_char(target_char)):
            exit(FORMAT_ERROR)

    ##
    # @brief filters white chars and comments and then check for
    #   for special character used as separator of closing of
    #   current component ('}')
    # @return read char
    def read_separator(self):
        self.filter_whitespace()
        if not(self.is_char(CHAR_SEPARATOR) or self.is_char(CHAR_CLOSED)):
            exit(FORMAT_ERROR)
        return self.char

    ##
    # @brief reads character for beginning of component '{'
    def read_open(self):
        self.read_char(CHAR_OPEN)

    ##
    # @param target_char - character for comparison
    # @return True if current char is equal to character for comparison
    def is_char(self, target_char):
        return self.char == target_char

    ##
    # @return True for current char is empty string (end of file in python)
    def is_eof(self):
        return self.is_char(CHAR_EOF)

    ##
    # @return True when current char is comment
    def is_comment(self):
        return self.is_char(CHAR_COMMENT)

    ##
    # @return True when current char is white char
    def is_whitespace(self):
        return self.char.isspace()

    ##
    # @return True if character is valid character in state string
    def is_valid(self):
        return self.char == CHAR_UNDERSCORE or self.char.isalnum()

    ##
    # READS STATE
    # @brief filters white chars and comments from input file and then reads
    #   state (checked by format rules)
    # @return string containing state
    def read_state(self):
        self.str = ''
        self.read()
        self.filter_whitespace()
        if self.is_char(CHAR_CLOSED):
            return self.str

        if not self.char.isalpha():
            sys.stderr.write(ERR_INPUT_FILE_FORMAT)
            exit(FORMAT_ERROR)

        while self.is_valid():
            self.append_char()
            self.read()

        if self.str.endswith(CHAR_UNDERSCORE):
            exit(FORMAT_ERROR)

        return self.str

    ##
    # SUPPORTIVE METHOD FOR FILTERING SPECIAL CHARACTER
    # @brief reads special character (escaped by apostrophe)
    # @return special character string
    def filter_special_symbol(self):
        if self.is_char(CHAR_APOSTROPHE):
            self.read()
            if self.is_char(CHAR_APOSTROPHE):
                self.append_char()
            elif self.is_whitespace() or self.is_char(CHAR_SEPARATOR):
                return self.str
            else:
                exit(FORMAT_ERROR)

    ##
    # READS CHAR AND APPENDS IT TO FILEREADER STRING
    # @brief can read only specified char specified by parameter
    # @param target_char - default none can be used to read and append only
    #  specific character
    def read_and_append(self, target_char=None):
        if target_char is not None:
            self.read_char(target_char)
        else:
            self.read()
        self.append_char()

    ##
    # READS ALPHABET SYMBOL
    # @brief reads alphabets symbol from input file.
    #        Can escape special symbol like apostrohpe.
    # @param rule - true when reading symbol for rule
    #               (symbol can be followed by -> )
    # @return symbol in specification format
    def read_symbol(self, rule=False):
        self.str = ''
        self.filter_whitespace()
        if not self.is_char(CHAR_APOSTROPHE):
            self.read()
            self.filter_whitespace()

        if self.is_char(CHAR_CLOSED):
            return self.str
        elif not self.is_char(CHAR_APOSTROPHE):
            exit(FORMAT_ERROR)

        self.append_char()
        self.read_and_append()
        if self.is_char(CHAR_APOSTROPHE):
            self.read()
            if self.is_char(CHAR_APOSTROPHE):
                self.append_char()
            elif self.is_whitespace() or self.is_char(CHAR_SEPARATOR)\
                    or self.is_char(CHAR_CLOSED):
                return self.str
            elif rule and self.is_char('-'):
                return self.str
            else:
                exit(FORMAT_ERROR)
        elif self.is_char('\\'):
            self.read_and_append()
            if not(self.is_char('n') or self.is_char('t')):
                exit(FORMAT_ERROR)

        self.read_and_append()
        if not(self.is_char(CHAR_APOSTROPHE)):
            exit(FORMAT_ERROR)

        return self.str


##
# PARSING COMMAND LINE ARGUMENTS
# @brief - uses argparse module for checking arguments validity
#   and setting values of coresponding atributes in ArgumentParser object
# @return - args - object with parsed options
def parse_arguments():
    # help argument cannot be combined with other:
    if('--help' in sys.argv or '-h' in sys.argv)\
            and len(sys.argv) > 2:
        sys.stderr.write(ERR_ARGUMENT)
        exit(ARGUMENT_ERROR)
    # ArgumentParser object options setup
    parser = argparse.ArgumentParser(prog='dka', description=DKA_HELP_DESC)
    parser.add_argument('--input', help=HELP_INPUT)
    parser.add_argument('--output', help=HELP_OUTPUT)
    parser.add_argument('-i', '--case-insensitive', action='store_true',
                        help=HELP_CASE_INSENSITIVE)
    parser.add_argument('-r', '--rules-only', action='store_true',
                        help=HELP_RULES_ONLY)
    parser.add_argument('-w', '--white-char', action='store_true',
                        help=HELP_WHITE_CHAR)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('-e', '--no-epsilon-rules', action='store_true',
                      help=HELP_NO_EPSILON_RULES)
    mode.add_argument('-d', '--determinization', action='store_true',
                      help=HELP_DETERMINIZATION)
    mode.add_argument('--analyze-string', action='store', dest='string',
                      default=False, help=HELP_ANALYZE_STRING)
    mode.add_argument('--wsfa', action='store_true', help=HELP_WSFA)
    # Parse argv using prepared ArgumentParser and handle parsing error
    try:
        args = parser.parse_args()
    except SystemExit:
        if '--help' in sys.argv or '-h' in sys.argv:
            exit(GUTT)
        sys.stderr.write(ERR_ARGUMENT)
        exit(ARGUMENT_ERROR)
    return args


##
# OUTPUT FILE HANDLING
# @param args - program arguments parsed by argparser
# @brief - provides output file for saving result
# @return - opened output file
# @return default - stdout if output file not specified by argument
def get_output_file(args):
    if args.output is None:
        return sys.stdout
    try:
        output_file = open(args.output, 'w', encoding=ENCODING)
    except IOError:
        sys.stderr.write(ERR_OPENING_OUT)
        exit(OUTPUT_ERROR)
    return output_file


##
# MAIN FUNCTION
# @param args - program arguments parsed by argparser
# @brief main function of DKA project - reads formal specification
#        of FA from input file (using FileReader), transforms it
#        depending on arguments and writes result to output file
def main():
    args = parse_arguments()
    # get input and output file
    input_file = FileReader(args.input, args.case_insensitive)
    output_file = get_output_file(args)
    # get finite automaton specification from file
    automaton = FiniteAutomaton()
    automaton.load(input_file, args.rules_only)

    # remove epsilon rules:
    if args.no_epsilon_rules or args.determinization \
            or args.string is not False or args.wsfa:
        automaton.remove_epsilon_rules()

    # determinizate FA:
    if args.determinization or args.string is not False or args.wsfa:
        automaton.determinize()

    # analyze given string:
    if args.string is not False:
        output_file.write(STRING_ACCEPTED if automaton.analyze_string(args.string)
                          else STRING_NOT_ACCEPTED)
    else:
        # transform FA to well specified FA
        if args.wsfa:
            automaton.remove_unacceptable_states()
            automaton.transform_to_complete(args.case_insensitive)
        # write result to output file
        automaton.print(output_file)

    # everything went better than expected:
    output_file.close()

##
# MAIN
if __name__ == '__main__':
    main()

