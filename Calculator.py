#!/home/vesper/.miniconda3/bin/python

'''
Author              : Barry Penner | COMP 5361 | Fall 2023 | G. Grahne | programming assignment 2

Introduction        : This module implements a basic but comprehensive parser and evaluator for mathematical expressions
                      and propositional statements. All functionality is fully contained within the Calculator class,
                      which exposes a single method, noteval(), to parse and evaluate a given expression. All other 
                      classes provide support functionality (TUI, testing, definitions, etc.).

Approach            : Convert provided infix expression to postfix (Reverse Polish) notation, using Shunting Yards
                      algorithm. Then, evaluate converted expression using a stack

Key methods         : Calculator class: tokenize(), shunt_to_rpn(), rpn_evaluator(). SimpleStack class.

Sources             : https://www.andreinc.net/2010/10/05/converting-infix-to-rpn-shunting-yard-algorithm
                    : https://en.wikipedia.org/wiki/Shunting_yard_algorithm

User Interface      : Run this program in your terminal with no arguments to see available options and flags.
                    : If using *nix, be sure to edit permissions (and shebang line if using PATH).

Variable assignment : Dictionary-based variable assignments are accepted as a parameter in direct calls to the noteval()
                      method, but they are not required. If you wish to test this directly, then create a Calculator()
                      object in Python's native REPL and call Calculator.noteval() directly.
                    : Dictionary-based variable assignment is not otherwise supported in the provided CLI user interface.

Diagnostics         : If evaluation errors are encountered, a diagnostics table can be printed. Access this table by
                      passing the argument `diagnose=<bool>` to noteval(), or in the TUI by running the program with the
                      option combination `single diagnose`.

Testing             : This program passes all tests included with the assignment. In order to run tests externally,
                      ensure that the `test_main.py` file imports the correct module name and that each test calls the
                      `Calculator.Tests` class correctly, then run the unittest module as usual.
                    : You may also run the expanded test suite included in this module by running the program from the
                      command line with the `tests` modifier. Secondary modifiers (optional) are:
                      t: unittests only (all original assignment tests, plus an expanded set of arithmetic tests)
                      a: assignment tests (the four propositional statements required in the assignment)
                      d: demonstration tests and evaluations, highlighting the evaluator's flexibility and output options

Known issues        : I had to stop developing this program and move on to other assignments, work, etc., so bugs and
                      errors remain. In general,
                    : Error handling is very minimal, and expression input is not validated. Crashes have little grace.
                    : Edge cases are not well tested. More complex expressions may expose unexpected errors.
                    : The CLI interface is functional, but fragile.
                    : Environment management is not implemented at all.
                    : Bad practice to include a test package within same file as testable code; in this case, CLI args
                      interfere with the call to unittest.main()  solution: delete args from sys.argv[] if tests are
                      called. Ugly little hack.

Closing comment     : I am very interested in systems programming, and took advantage of this assignment to explore
                      parsing and evaluation processes in more depth than is required. Truth is I spent far too much
                      time on this... so I hope you enjoy it, despite it being simultaneously an overengineered
                      deliverable and a very naive implementation of a true parser & evaluator.
                      Also, I hope this program can provide to you a better perspective on my capability than my
                      awful midterm grade.
'''


from typing import Dict, List
import sys
from math import sin, cos, tan, sqrt, log
from math import factorial as fact
from math import radians as rad
from math import degrees as deg
from copy import deepcopy as dcopy
import unittest


def main():
    cli(sys.argv).run()
    # calc = Calculator()
    # calc.noteval("!!p1", {'p1':True}, verbose='result')
    return


class Calculator:
    '''
    This class encapsulates all functionality for evaluating simple, generalized math statements and propositional sentences.

    All functionality is provided through the noteval() method.

    All logical tokens must be delimited by spaces, with the exception of the following: ( ) ! ~ , ^

    Operators are UPPERCASE, constants are UPPER or lowercase

    Mathematical statements can have arbitrary nesting and complexity, as long as nesting parentheses are matched correctly.

    Braces {} and brackets[] are not supported.

    Supported binary operators  **      : exponent
                                ^       : also exponent
                                *
                                /
                                %       : modulo
                                //      : floor division
                                +
                                -       : subtraction
                                LOG     : logarithm. Form: LOG(exp, base) :: exp and base can be compound expressions
                                RND     : round. Form: RND(value, int) :: value can be compound
                                <
                                >
                                <=
                                >=
                                ==
                                !=
                                AND
                                &
                                OR
                                |
                                ,       : separator for functions that require multiple arguments; currently, only LOG
                                IF
                                ->
                                IFF
                                <->

    Supported unary operators   NOT
                                !
                                ~       : numerical negation
                                SIN
                                COS
                                TAN
                                ABS
                                SQRT
                                FACT    : factorial
                                RAD     : radians :: convert from degrees
                                DEG     : degrees :: convert from radians

    Boolean operands            True
                                False

    Keywords                    ANS     : returns previous evaluation result to variable in next expression; available in NotRepl() only

    Constants                   _PI     : (or _pi) pi to standard precision :: 3.141592653589793
                                _E      : (or _e)  e  to standard precision :: 2.718281828459045

    '''

    def __init__(self, input=None, verbose=None):
        self.expression     = None # raw expression as provided. Must be as infix notation.
        self.variables      = None # variable assignments, if provided
        self.tokenized      = None # split by parens and whitespace
        self.rpn            = None # reverse polish notation (postfix) representation of expression
        self.unique_tokens  = None # set of unique non-operator and non-boolean tokens in expression; includes numbers and variables
        self.expr_type      = None # if True, expr type is MATH; if False, expr type is BOOLEAN
        self.result         = None # result of expression evaluation; if type is math: result = number. If type is boolean: result is boolean if variables assigned, else string
        self.truthtable     = None # string representation of the complete truth table for a boolean expression
        self.diagnostics    = None # list of strings representation of every call to _rpn_eval() made during evaluation
        self.details        = None # string representation of expression parsing and evaluation


    def reset(self):
        '''
        caller : external
        input  : none
        action : reset all instance variables so that same instance can be used for multiple calls.
        return : none
        '''
        self.expression     = None
        self.variables      = None
        self.tokenized      = None
        self.rpn            = None
        self.unique_tokens  = None
        self.expr_type      = None
        # self.result         = None
        self.truthtable     = None
        self.diagnostics    = None
        self.details        = None


    def noteval(self, expression: str, variables: dict[str,bool]=None, verbose: str='return', diagnose: bool=False) -> bool | float | str:
        '''
        caller  : external
        input   : self; str, an infix expression, either a propositional sentence or a mathematical statement; optional for propositional sentences: dict, with variable assignments
        action  : converts statement into postfix notation; isolates all non-operator and non-boolean tokens; evaluates expression by calling the appropriate evaluator method.
        return  : result. If mathematical statement: returns float. If propositional sentence: returns boolean if variables provided, or returns string if no variables provided.
        options : verbose: str; defines standard output. 'return': none, 'result': same as return value, 'summary': key information incl. truth table, 'complete': all information; default is 'return'.
                : diagnose: bool; optional print to standard out of individual calls to _rpn_eval() method.
        '''
        self.expression     = expression
        self.variables      = variables
        self.tokenized      = self.tokenize(expression)
        self.rpn            = self.shunt_to_rpn(self.tokenized)
        self.unique_tokens  = sorted(list(self.extract_vars(self.rpn)))
        self.expr_type      = self.math_or_bool(self.unique_tokens)
        self.diagnostics    = []
        if self.expr_type:
            self.math_expr_eval(expression)
        else:
            if not variables or type(variables) == type([]):
                self.bool_expr_table(expression)
            else:
                self.bool_expr_eval(expression, variables)
        self.details = self.showtime(verbose)
        if self.details:
            print(self.details)
        if diagnose:
            print()
            print(self.diagnose())
        if self.result in {'true', 'false'}:
            return self.str2bool(self.result)
        if verbose != 'return':
            return
        return self.result


    def math_expr_eval(self, expr: str) -> None:
        '''
        caller : noteval()
        input  : self; str, infix expression
        action : evaluate a mathematical infix expression via postfix conversion and stack manipulation
        return : None. Assign result to instance variable
        '''
        result = self.rpn_evaluator(self.rpn)
        if isinstance(result, str):
            self.result = result
        elif isinstance(result, float):
            self.result = int(result) if result.is_integer() else result
            return
        elif isinstance(result, int):
            self.result = result
        else:
            self.result = self.str2bool(result)
        return


    def bool_expr_eval(self, expr: str, vars: dict[str, bool]) -> None:
        '''
        caller : noteval()
        input  : self; str, infix expression; dict, variable definitions
        action : evaluate a boolean infix expression via postfix conversion and stack manipulation
        return : None. Print result to STDOUT
        '''
        rpn_swapped = self.variable_swap(self.rpn, vars)
        self.result = self.rpn_evaluator(rpn_swapped)
        return


    def bool_expr_table(self, expr: str, tableOnly: bool=False) -> None:
        '''
        caller : noteval(), showtime()
        input  : self; str, infix expression
        action : evaluate a boolean infix expression to all possible truth values via postfix conversion and stack manipulation
        return : None. Print result to STDOUT
        '''
        seed_matrix = self.create_seed_matrix(len(self.unique_tokens)) # boolean seed values, altered in-place to generate return value
        results     = [] # boolean results, only used to evaluate contingency/tautology/contradiction
        if tableOnly:
            seed_matrix = [[val for val in self.variables.values()]]
        # loop through seed matrix: for each row, build substitution dictionary, evaluate, and append result to row.
        for r, row in enumerate(seed_matrix):
            rpn_swap = dcopy(self.rpn)
            sub_map = {}
            for n, var in enumerate(self.unique_tokens):
                sub_map[self.unique_tokens[n]] = seed_matrix[r][n]
            rpn_swap = self.variable_swap(rpn_swap, sub_map)
            result = self.rpn_evaluator(rpn_swap)
            results.append(result)
            row.append(result)
            del(rpn_swap)
        # determine if tautology / contingency / contradiction
        if not tableOnly:
            if 'true' not in results:
                self.result = 'contradiction'
            elif 'false' not in results:
                self.result = 'tautology'
            else:
                self.result = 'contingency'
        # construct table
        uniques = dcopy(self.unique_tokens)
        uniques.append('result')
        seed_matrix.insert(0, uniques)
        self.truthtable = self.tableBuilder(seed_matrix)
        return


    def tokenize(self, expr: str, subs: dict[str, bool]=None) -> list[str]:
        '''
        caller : noteval()
        input  : self; string, representing an infix expression
        action : extracts individual tokens as strings, preserving order
                 tokens: standard parentheses
                         mathematical and logical operators
                         any collection of characters not separated by whitespace
        return : list, representing tokens of an infix expression
        '''
        tokenized = []
        buffer = []
        for n, char in enumerate(expr):
            if char == ' ':
                if buffer:
                    tokenized.append(''.join(buffer))
                    buffer = []
                continue
            if char in Operators.singles:
                if (char == '!') and expr[n+1] == '=':
                    buffer.append(char)
                    continue
                if buffer:
                    tokenized.append(''.join(buffer))
                    buffer = []
                tokenized.append(char)
                continue
            buffer.append(char)
        if buffer:
            tokenized.append(''.join(buffer))  # last char/token of input string
        tokenized = self._control_case(tokenized)
        if subs:
            tokenized = self.variable_swap(tokenized, subs)
        return tokenized


    def shunt_to_rpn(self, tokens: list[str]) -> list[str]:
        '''
        caller : noteval()
        input  : self; list, representing tokens of an infix expression
        action : reorders tokens according to operator precedence and parenthesis nesting rules into Reverse Polish Notation (postfix notation)
        return : list, representing tokens of a postfix expression
        source : (pseudocode) https://en.wikipedia.org/wiki/Shunting_yard_algorithm
        source : (pseudocode and Java code) https://www.andreinc.net/2010/10/05/converting-infix-to-rpn-shunting-yard-algorithm
        '''
        operators   = Operators.both # dict :: operator[i] = ( int(precedence), str(associativity) )
        rpn         = []
        op_stack    = SimpleStack()
        for token in tokens:
            if token in operators.keys():
                top = op_stack.peek()
                while not op_stack.isEmpty() \
                      and op_stack.peek() in operators.keys() \
                      and ( ((operators[token][1] == 'L') and (operators[top][0] >= operators[token][0])) \
                         or ((operators[token][1] == 'R') and (operators[top][0] > operators[token][0])) ):
                    rpn.append(op_stack.pop())
                    top = op_stack.peek()
                op_stack.push(token)
                continue
            elif token == '(':
                op_stack.push(token)
                continue
            elif token == ')':
                while op_stack.peek() != '(' and not op_stack.isEmpty():
                    rpn.append(op_stack.pop())
                if op_stack.peek() == '(':
                    op_stack.pop()
                # if op_stack.peek() in operators: // these two lines are wrong
                #     rpn.append(op_stack.pop())   // typo! do not include.
                continue
            elif token == ',':
                while op_stack.peek() != '(':
                    rpn.append(op_stack.pop())
                continue
            else:
                rpn.append(token)
        while not op_stack.isEmpty():
            if op_stack.peek() != '(':
                rpn.append(op_stack.pop())
        return rpn


    def rpn_evaluator(self, rpn: list[str], table:bool=False) -> bool | int:
        '''
        caller : math_expr_eval(), bool_expr_eval(), bool_expr_table()
        input  : self; list, representing tokens of a postfix expression
        action : uses a stack to evaluate a postfix expression
                 individual calculations are handled via a match
                 statement implemented in the helper method _rpn_eval()
        return : boolean or int, dependent on provided expression
        '''
        eval_stack = SimpleStack()
        binary_ops = Operators.binary
        unary_ops  = Operators.unary
        keywords   = Operators.keywords
        constants  = Operators.constants
        rows       = {}
        diagnostic = []
        try:
            for token in rpn:
                if token.upper() in constants.keys():
                    eval_stack.push(constants[token.upper()])
                elif token in binary_ops:
                    rhs = eval_stack.pop()
                    lhs = eval_stack.pop()
                    result = self._rpn_eval(lhs, rhs, token)
                    diagnostic.append(f"token: {token:<5} lhs: {lhs:<6} rhs: {rhs:<7} result: {result}")
                    eval_stack.push(result)
                    if table:
                        rows[(lhs, token, rhs)] = result
                elif token in keywords:
                    if token == 'ANS':
                        eval_stack.push(self.result)
                elif token in unary_ops:
                    val = eval_stack.pop()
                    result = self._rpn_eval(None, val, token)
                    diagnostic.append(f"token: {token:<5} val: {val:<19} result: {result}")
                    eval_stack.push(result)
                    if table:
                        rows[(None, token, val)] = result
                else:
                    eval_stack.push(token)
        except TypeError as e:
            return f"{type(e).__name__}: {e}"
        self.diagnostics.append('\n'.join(diagnostic))
        if table:
            return rows
        return eval_stack.pop()


    def _rpn_eval(self, lhs: str, rhs: str, op: str) -> bool | int:
        '''
        caller : rpn_evaluator()
        input  : self; two operands (lhs, rhs) as either booleans or strings and one operator in string form
        action : convert provided value to boolean if necessary
                 perform calculation on operands as determined by the provided operator, and return result
                 convert result back to string if necessary
        return : boolean or int, dependent on provided expression
        '''
        if lhs == 'true' or lhs == 'false':
            lhs = self.str2bool(lhs)
        if rhs == 'true' or rhs == 'false':
            rhs = self.str2bool(rhs)
        match(op):
            case '**':
                return pow(float(lhs), float(rhs))
            case '^':
                return pow(float(lhs), float(rhs))
            case '*':
                return float(lhs) * float(rhs)
            case '/':
                return float(lhs) / float(rhs)
            case '%':
                return float(lhs) % float(rhs)
            case '//':
                return float(lhs) // float(rhs)
            case '+':
                return float(lhs) + float(rhs)
            case '-':
                return float(lhs) - float(rhs)
            case 'SIN':
                return sin(float(rhs))
            case 'COS':
                return cos(float(rhs))
            case 'TAN':
                return tan(float(rhs))
            case 'RAD':
                return rad(float(rhs))
            case 'DEG':
                return deg(float(rhs))
            case 'ABS':
                return abs(float(rhs))
            case 'SQRT':
                return sqrt(float(rhs))
            case 'FACT':
                return fact(int(rhs))
            case 'LOG':
                return log(float(lhs), float(rhs))
            case 'RND':
                return round(float(lhs), int(rhs))
            case '~':
                return -abs(float(rhs))
            case 'NOT':
                return str(not rhs).lower()
            case '!':
                return str(not rhs).lower()
            case '<':
                return str(float(lhs) < float(rhs)).lower()
            case '>':
                return str(float(lhs) > float(rhs)).lower()
            case '<=':
                return str(float(lhs) <= float(rhs)).lower()
            case '>=':
                return str(float(lhs) >= float(rhs)).lower()
            case '==':
                return str(float(lhs) == float(rhs)).lower()
            case '!=':
                return str(float(lhs) != float(rhs)).lower()
            case 'AND':
                return str(lhs and rhs).lower()
            case '&':
                return str(lhs and rhs).lower()
            case 'OR':
                return str(lhs or rhs).lower()
            case '|':
                return str(lhs or rhs).lower()
            case 'IF':
                return str(True if ((not lhs) or (lhs and rhs)) else False).lower()
            case '->':
                return str(True if ((not lhs) or (lhs and rhs)) else False).lower()
            case 'IFF':
                return str(True if (lhs == rhs) else False).lower()
            case '<->':
                return str(True if (lhs == rhs) else False).lower()
            # case ',':
            #     pass
            case _:
                return None


    def showtime(self, verbose: str='return') -> None:
        '''
        caller  : noteval()
        input   : str, describing requested level of verbose
                  for param verbose:
                      arg return   : do not print anything
                      arg result   : only the numeric or boolean result
                      arg table    : print truth table only; generate table if needed
                      arg summary  : core information about expression and solution generation
                      arg complete : all information
        action  : compile (generate where needed) requested information into a string and return it.
        return  : str; returns a string representation
        '''
        output = []
        match(verbose):
            case 'return':
                return None
            case 'result':
                output.append(f"{self.result}")
                return '\n'.join(output)
            case 'table':
                output.append(f"expression: {self.expression}")
                if self.expr_type:
                    output.append('table not available.')
                elif self.truthtable:
                    output.append(f"{self.truthtable}")
                else:
                    self.bool_expr_table(self.expression, tableOnly=True)
                    output.append(f"{self.truthtable}")
                return '\n'.join(output)
            case 'summary':
                output.append(f"solving   :  {self.expression}")
                output.append(f"variables :  {'not provided.' if not self.variables else ', '.join([str(k)+':'+str(v) for k, v in self.variables.items()])}")
                output.append(f"postfix   :  {' '.join(self.rpn)}")
                output.append(f"result    :  {self.result}")
                return '\n'.join(output)
            case 'complete':
                output.append(f"expression              : {self.expression}")
                output.append(f"variables               : {'not provided.' if not self.variables else ', '.join([str(k)+':'+str(v) for k, v in self.variables.items()])}")
                output.append(f"tokens                  : {'  '.join(self.tokenized)}")
                output.append(f"reverse Polish notation : {'  '.join(self.rpn)}")
                output.append(f"unique tokens           : {', '.join(self.unique_tokens)}")
                output.append(f"expression type         : {'math' if self.expr_type else 'boolean'}")
                output.append(f"result                  : {self.result}")
                if self.expr_type:
                    output.append('truth table             : table not available.')
                elif self.truthtable:
                    output.append(f"truth table:")
                    output.append(f"{self.truthtable}")
                else:
                    self.bool_expr_table(self.expression, tableOnly=True)
                    output.append(f"truth table:")
                    output.append(f"{self.truthtable}")
                return '\n'.join(output)
            case _:
                print(f"argument {verbose} not recognized.")
                sys.exit(0)


    def get_table(self) -> str:
        return self.truthtable


    def tableBuilder(self, arrays: list[list], buffer=10) -> str:
        '''
        caller : bool_expr_table()
        input  : self; list of lists, representing a matrix
        action : create a formatted string that, when printed, shows a table of the contents of the list of lists
        return : string
        '''
        result = [] # array of strings to print when finished
        # build header:
        labels = arrays[0]
        header = ["|"]
        for item in labels:
            fitted = f"{str(item).center(buffer, ' ')}|"
            header.append(fitted)
        header.append("\n|" + "-"*((buffer+1)*len(labels)-1) + "|")
        result.append("".join(item for item in header))
        # build table body:
        body = []
        for row in arrays[1:]:
            line = ["|"]
            for item in row:
                fitted = f"{str(item).center(buffer, ' ')}|"
                line.append(fitted)
            line = "\n" + "".join(item for item in line)
            body.append(line)
        result.append("".join(item for item in body))
        result = "".join(item for item in result)
        return result


    def math_or_bool(self, unique_tokens: list[str]) -> bool:
        '''
        caller : noteval()
        input  : self; list, of all unique tokens in an expression that are not operators or booleans
        action : check each provided tokens that are not part of the set that define real numbers
        return : bool; False -> not a math expression; True -> math expression
        '''
        digits = {'1','2','3','4','5','6','7','8','9','0','.'}
        for token in unique_tokens:
            if token.upper() in Operators.constants.keys():
                continue
            for char in token:
                if char not in digits:
                    return False
        return True


    def variable_swap(self, tokenlist: list[str], assignments: dict[str, bool]) -> list[str]:
        '''
        caller : bool_expr_eval(), bool_expr_table(), tokenize()
        input  : self; list, representing infix tokens; dict, representing variable assignments.
        action : local helper: assign values from dict to concomitant variables.
        return : list, representing infix tokens, with values replacing variables.
        '''
        for key, val in assignments.items():
            for n, token in enumerate(tokenlist):
                if token == key:
                    tokenlist[n] = str(val).lower()
        return tokenlist


    def _control_case(self, tokenlist: list[str]) -> list[str]:
        '''
        caller : tokenize()
        input  : self; list, representing infix tokens
        action : convert lettered operators with upper case
        return : list, representing infix tokens
        '''
        for n, token in enumerate(tokenlist):
            if token.upper() in ['AND', 'OR', 'NOT', 'IF', 'IFF',]:
                tokenlist[n] = token.upper()
        return tokenlist


    def str2bool(self, token: str) -> bool:
        '''
        caller : _rpn_eval(), noteval()
        input  : self; str, representing a boolean token
        action : convert string token to the appropriate boolean object
        return : bool, single object
        '''
        if not token:
            return
        if token.lower() == 'true':
            return True
        elif token.lower() == 'false':
            return False
        else:
            raise ValueError(f"boolean: invalid truth value {token}.")


    def extract_vars(self, rpn: list[str]) -> set():
        '''
        caller : noteval()
        input  : self; list, representing tokenized postfix notation for an expression.
        action : iterate through list and count the number of unique variables in the expression.
        return : int, number of unique variables
        '''
        unique = set()
        for item in rpn:
            if item not in Operators.all_ops_kwds:
                unique.add(item)
        return unique


    def create_seed_matrix(self, var_count: int) -> list[list[bool]]:
        '''
        caller : bool_expr_table()
        input  : self; int, count of unique variables in an expression
        action : generate a matrix of boolean values that satisfies all permutations of an expression.
        return : list of lists, each representing one row of assignable truth values to an expression
        '''
        matrix = []
        for i in range(1, var_count+1):
            arr = []
            for j in range(int(pow(2, var_count-i))):
                for k in range(int(pow(2,i)/2)):
                    arr.append('true')
                for m in range(int(pow(2,i)/2)):
                    arr.append('false')
            matrix.append(arr)
        matrix = list(map(list, zip(*matrix)))
        for lst in matrix:
            lst = lst.reverse()
        return matrix


    def diagnose(self) -> None:
        '''
        caller : noteval()
        input  : self
        action : concatenate the contents of self.diagnostics and return the string
        return : str, representing each call to _rpn_eval() during program execution
        '''
        output = []
        n = len(self.diagnostics)
        labels = [f"block {m}" for m in range(n)]
        output.append(f"~~~~~~~~~~~~~~~~~~ START DIAGNOSTIC ~~~~~~~~~~~~~~~~~~\n"
                      f"Each block (if more than one) represents all calls to\n"
                      f"_rpn_eval() by rpn_evaluator() during execution.")
        for i in range(n):
            output.append(f"\n\nblock {i+1}:\n")
            output.append(self.diagnostics[i])
        output.append(f"\n~~~~~~~~~~~~~~~~~~ END DIAGNOSTIC ~~~~~~~~~~~~~~~~~~\n")
        return ''.join(output)


class SimpleStack:
    '''
    Stack data structure implemented using a linked list.
    '''
    def __init__(self):
        self.head = None
        self.length = 0

    def push(self, data):
        new = Node(data)
        if self.head is not None:
            new.next = self.head
        self.head = new
        self.length += 1
        return

    def pop(self):
        if self.head is None:
            # print("pop: stack is empty.")
            return
        rtval = self.head.data
        self.head = self.head.next
        self.length -= 1
        return rtval

    def peek(self):
        if self.head is None:
            return None
        return self.head.data

    def isEmpty(self):
        return True if self.head is None else False

    def getLength(self):
        return self.length

    def display(self):
        if self.length == 0:
            return "display: stack is empty."
        buffer = []
        current = self.head
        while current.next is not None:
            buffer.insert(0, current.data)
            current = current.next
        buffer.insert(0, current.data)
        return ' '.join(buffer)


class Node:
    '''
    node class for SimpleStack
    '''
    def __init__(self, data):
        self.data = data
        self.next = None


class Operators:
    '''
    Reference class for operators
    '''
    keywords       = ['ANS',]
    boolean        = ['true', 'false']
    unary          = {'NOT' : (11,'R'),
                      '!'   : (11,'R'),
                      'SIN' : (11,'R'),
                      'COS' : (11,'R'),
                      'TAN' : (11,'R'),
                      'RAD' : (11,'R'),
                      'DEG' : (11,'R'),
                      'ABS' : (11,'R'),
                      'SQRT': (11,'R'),
                      'FACT': (11,'R'),
                      '~'   : (10,'R'),
                      }
    binary         = {'LOG' : (11,'R'),
                      'RND' : (11,'R'),
                      '**'  : (9,'R'),
                      '^'   : (9,'R'),
                      '*'   : (8,'L'),
                      '/'   : (8,'L'),
                      '%'   : (8,'L'),
                      '//'  : (8,'L'),
                      '+'   : (7,'L'),
                      '-'   : (7,'L'),
                      '<'   : (6,'L'),
                      '>'   : (6,'L'),
                      '<='  : (6,'L'),
                      '>='  : (6,'L'),
                      '=='  : (5,'L'),
                      '!='  : (5,'L'),
                      'AND' : (4,'L'),
                      '&'   : (4,'L'),
                      'OR'  : (3,'L'),
                      '|'   : (3,'L'),
                      'IF'  : (1,'L'),
                      '->'  : (1,'L'),
                      'IFF' : (0,'L'),
                      '<->' : (0,'L'),
                      }
    both           = {**binary, **unary}
    all_ops_kwds   = [*binary.keys(), *unary.keys(), *boolean, *keywords]
    constants      = {'_PI': 3.141592653589793, '_E': 2.718281828459045}
    singles        = ['(', ')', '!', '~', ',', '^']


class cli:
    '''
    Implements a naive text-based user interface. Called directly from main()
    '''

    def __init__(self, args):
        self.args = args

    def run(self):
        if len(self.args) == 1:
            print("Welcome to Calculator. Please choose:")
            print("  run tests and demos        : tests")
            print("  run notrepl                : nrepl")
            print("  evaluate single expression : single")
            print("  show available operators   : operators")
            print("  exit program               : exit\n>> ", end=' ')
            ui = input()
            mod = None
        elif len(self.args) == 2:
            ui = self.args[1]
            mod = None
        elif len(self.args) == 3:
            ui = self.args[1]
            mod = self.args[2]
        else:
            print("Too many arguments.\nAvailable args: tests | nrepl | single | exit\nAborting.")
            return
        
        if ui not in ['tests', 'nrepl', 'single', 'operators', 'exit']:
            print(f"Unrecognized argument: {ui}\naborting.")
            return
        elif ui == 'tests':
            del(self.args[1:3]) # args interfere with call to unittest.main()
            demo = Demonstrate()
            if not mod or mod == '-t':
                demo.test_demo()
            if not mod or mod == '-a':
                demo.assignment_questions(verbose='summary')
            if not mod or mod == '-d':
                demo.general_demo()
            del(demo)
            return
        elif ui == 'single':
            expr = input("enter an expression: >> ")
            verb = input("enter a verbose level: (result/summary/table/complete) >> ")
            calc = Calculator()
            if mod != 'diagnose':
                diagnose = False
            else:
                diagnose = True
            calc.noteval(expr, verbose=verb, diagnose=diagnose)
            del(calc)
            return
        elif ui == 'nrepl':
            NotRepl().loop()
            return
        elif ui == 'operators':
            print('  '.join(Operators.all_ops_kwds))
            print(f"singles: {'  '.join(Operators.singles)}")
            return
        else:
            print("exiting.")
            return


class TestMainMethods(unittest.TestCase):
    '''
    Unit test class provided with assignment.
    Modifications:  (1) added two blocks of tests in test_evaluate_statement(): math questions, and propositional sentences from the assignment.
                    (2) changed `main.` to `Tests.` to call function directly within this module.
    '''
    def test_evaluate_statement(self):
        self.assertEqual(Tests.evaluate_statement('P1 -> P2', {'P1': True, 'P2': False}), False)
        self.assertEqual(Tests.evaluate_statement('P1 -> ( P2 OR NOT P3 )', {'P1': True, 'P2': False, 'P3': True}), False)
        self.assertEqual(Tests.evaluate_statement('( NOT P1 AND ( P1 OR P2 ) ) IF P2', {'P1': False, 'P2': False}), True)
        self.assertEqual(Tests.evaluate_statement('( NOT P1 AND ( P1 OR P2 ) ) IF P2', {'P1': False, 'P2': True}), True)
        self.assertEqual(Tests.evaluate_statement('( NOT P1 AND ( P1 OR P2 ) ) IF P2', {'P1': True, 'P2': False}), True)
        self.assertEqual(Tests.evaluate_statement('( NOT P1 AND ( P1 OR P2 ) ) IF P2', {'P1': True, 'P2': True}), True)
        self.assertEqual(Tests.evaluate_statement('P2 AND ( P1 IF NOT P2 ) AND ( NOT P1 IF NOT P2 )', {'P1': True, 'P2': True}), False)
        self.assertEqual(Tests.evaluate_statement('P2 AND ( P1 IF NOT P2 ) AND ( NOT P1 IF NOT P2 )', {'P1': True, 'P2': False}), False)
        self.assertEqual(Tests.evaluate_statement('P2 AND ( P1 IF NOT P2 ) AND ( NOT P1 IF NOT P2 )', {'P1': False, 'P2': True}), False)
        self.assertEqual(Tests.evaluate_statement('P2 AND ( P1 IF NOT P2 ) AND ( NOT P1 IF NOT P2 )', {'P1': False, 'P2': False}), False)
        self.assertEqual(Tests.evaluate_statement('( P1 IF ( P2 IF P3 ) ) IF ( ( P1 IF P2 ) IF P3 )', {'P1': True, 'P2': True, 'P3': True}), True)
        self.assertEqual(Tests.evaluate_statement('( P1 IF ( P2 IF P3 ) ) IF ( ( P1 IF P2 ) IF P3 )', {'P1': True, 'P2': True, 'P3': False}), True)
        self.assertEqual(Tests.evaluate_statement('( P1 IF ( P2 IF P3 ) ) IF ( ( P1 IF P2 ) IF P3 )', {'P1': False, 'P2': True, 'P3': False}), False)
        self.assertEqual(Tests.evaluate_statement('( P1 IF ( P2 IF P3 ) ) IF ( ( P1 IF P2 ) IF P3 )', {'P1': True, 'P2': False, 'P3': False}), True)
        self.assertEqual(Tests.evaluate_statement('( P1 IF ( P2 IF P3 ) ) IF ( ( P1 IF P2 ) IF P3 )', {'P1': True, 'P2': False, 'P3': True}), True)
        self.assertEqual(Tests.evaluate_statement('( P1 IF ( P2 IF P3 ) ) IF ( ( P1 IF P2 ) IF P3 )', {'P1': False, 'P2': False, 'P3': True}), True)
        self.assertEqual(Tests.evaluate_statement('( P1 IF ( P2 IF P3 ) ) IF ( ( P1 IF P2 ) IF P3 )', {'P1': False, 'P2': True, 'P3': True}), True)
        self.assertEqual(Tests.evaluate_statement('( P1 IF ( P2 IF P3 ) ) IF ( ( P1 IF P2 ) IF P3 )', {'P1': False, 'P2': False, 'P3': False}), False)
        self.assertEqual(Tests.evaluate_statement('1 + 3'), 4)
        self.assertEqual(Tests.evaluate_statement('6 ** 2 + 2 * 6 * 8 + 8 ** 2'), 196)
        self.assertEqual(Tests.evaluate_statement('((1 + 2) / 3) ** 4'), 1)
        self.assertEqual(Tests.evaluate_statement('(1 + 2) * (3 / 4) ** (5 + 6)'), 0.12670540809631348)
        self.assertEqual(Tests.evaluate_statement('((P1 & P2) | (P3 & true)) | ((!P1 & !P3) & P2)'), 'contingency')
        self.assertEqual(Tests.evaluate_statement('(NOT P1 AND (P1 OR P2)) IF P2'), 'tautology')
        self.assertEqual(Tests.evaluate_statement('P2 AND (P1 IF NOT P2) AND (NOT P1 IF NOT P2)'), 'contradiction')
        self.assertEqual(Tests.evaluate_statement('(P1 -> (P2 -> P3)) -> ((P1 -> P2) -> P3)'), 'contingency')
        self.assertEqual(Tests.evaluate_statement('!((A | B) & (!(A & B)))'), 'contingency')
        self.assertEqual(Tests.evaluate_statement('!(p1 & p2)'), 'contingency')
        self.assertEqual(Tests.evaluate_statement('p1 <-> (p2 & !p3)'), 'contingency')

    def test_statement_type(self):
        self.assertEqual(Tests.statement_type('( NOT P1 AND ( P1 OR P2 ) ) IF P2', ['P1', 'P2']), 'tautology')
        self.assertEqual(Tests.statement_type('P2 AND ( P1 IF NOT P2 ) AND ( NOT P1 IF NOT P2 )', ['P1', 'P2']), 'contradiction')
        self.assertEqual(Tests.statement_type('( P1 IF ( P2 IF P3 ) ) IF ( ( P1 IF P2 ) IF P3 )', ['P1', 'P2']), 'contingency')


class Tests:
    '''
    Methods defined in assignment, available for direct testing.
    '''
    def evaluate_statement(statement: str, propositional_variables: Dict[str, bool]=None) -> bool:
        evaluator = Calculator()
        return evaluator.noteval(statement, propositional_variables)
        del(evaluator)

    def generate_truth_table(statement: str, propositional_variables: List[str]=None):
        evaluator = Calculator()
        return evaluator.noteval(statement, propositional_variables, verbose='table')
        del(evaluator)

    def statement_type(statement: str, propositional_variables: List[str]=None) -> str:
        evaluator = Calculator()
        return evaluator.noteval(statement, propositional_variables)
        del(evaluator)


class Demonstrate:
    '''
    Demonstration methods
    '''
    def assignment_questions(self, verbose='result'):
        evaluator = Calculator()

        print(f"~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ question 1 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")
        demo_1 = evaluator.noteval('((P1 & P2) | (P3 & true)) | ((!P1 & !P3) & P2)', {'P1': True, 'P2': False, 'P3': True}, verbose=verbose)
        evaluator.reset()
        print()

        print(f"~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ question 2 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")
        demo_2 = evaluator.noteval('(NOT P1 AND (P1 OR P2)) IF P2', verbose=verbose)
        evaluator.reset()
        print()

        print(f"~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ question 3 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")
        demo_3 = evaluator.noteval('P2 AND (P1 IF NOT P2) AND (NOT P1 IF NOT P2)', verbose=verbose)
        evaluator.reset()
        print()

        print(f"~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ question 4 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")
        demo_4 = evaluator.noteval('(P1 -> (P2 -> P3)) -> ((P1 -> P2) -> P3)', verbose=verbose)
        evaluator.reset()
        print()


    def general_demo(self):
        evaluator = Calculator()

        print(f"~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ demo 1 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")
        print("Math expression, verbose=default value (return only) and explicit call to print result:")
        demo_1 = evaluator.noteval('2 + 3 - 4 * 5 / 6', verbose='return')
        print(f"result: {demo_1}")
        evaluator.reset()
        print()

        print(f"~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ demo 2 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")
        print("Propositional statement, no assigned variables, verbose='result' (prints return value only):")
        evaluator.noteval('!(p1 & p2)', verbose='result')
        evaluator.reset()
        print()

        print(f"~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ demo 3 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")
        print("Propositional statement, assigned variables, verbose='result' (prints return value only):")
        evaluator.noteval('P1 -> P2', {'P1': True, 'P2': False}, verbose='result')
        evaluator.reset()
        print()

        print(f"~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ demo 4 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")
        print("Simple math expression, verbose='summary':")
        evaluator.noteval('1 + 2', verbose='summary')
        evaluator.reset()
        print()

        print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ demo 5 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")
        print("Nested propositional statement, no assigned variables, verbose='table':")
        evaluator.noteval('(NOT P1 AND (P1 OR P2)) IF P2', verbose='table')
        evaluator.reset()
        print()

        print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ demo 6 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")
        print("Math expression, verbose='summary':")
        evaluator.noteval('6 ** 2 + 2 * 6 * 8 + 8 ** 2', verbose='summary')
        evaluator.reset()
        print()

        print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ demo 7 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")
        print("Numbers with boolean operators, verbose='result' (prints return value only):")
        evaluator.noteval('2 > 8', verbose='result')
        evaluator.reset()
        print()

        print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ demo 8 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")
        print("Numbers with boolean operators, verbose='summary':")
        evaluator.noteval('3 < !(2 >= 9) != 4', verbose='summary')
        evaluator.reset()
        print()

        print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ demo 9 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")
        print("Numbers with boolean operators, verbose='summary':")
        evaluator.noteval('3 < 2 or 11 >= 9', verbose='summary')
        evaluator.reset()
        print()

        print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ demo 10 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")
        print("Nested propositional statement with boolean values, no variables, verbose='summary':")
        evaluator.noteval('(true | false) & !(true & false)', verbose='summary')
        evaluator.reset()
        print()

        print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ demo 11 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")
        print("Nested propositional statement, assigned variables, verbose='complete':")
        evaluator.noteval('(A | B) & !(A & B)', {'A':True, 'B':False}, verbose='complete')
        evaluator.reset()
        print()

        print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ demo 12 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")
        print("Propositional statement, no assigned variables, verbose='complete':")
        evaluator.noteval('(A | B) & !(A & B)', verbose='complete')
        evaluator.reset()
        print()

        print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ demo 13 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")
        print("Simple mathematical negation, verbose='summary':")
        evaluator.noteval('~3', verbose='summary')
        evaluator.reset()
        print()

        print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ demo 14 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")
        print("Nested unary operators, verbose='summary':")
        evaluator.noteval('37 + SIN(40 + 5)', verbose='summary')
        evaluator.reset()
        print()

        print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ demo 15 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")
        print("Nested unary operators with boolean comparison, verbose='summary':")
        evaluator.noteval('37 + DEG (SIN (40 + 5)) >= 1', verbose='summary')
        evaluator.reset()
        print()

        print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ demo 16 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")
        print("Functions with comma-separated arguments, verbose='summary':")
        evaluator.noteval('LOG((25 * 4)^2,10)', verbose='summary')
        evaluator.reset()
        print()

        print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ demo 17 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")
        print("Constants, verbose='summary':")
        evaluator.noteval('_pi + LOG(_e, _e)', verbose='summary')
        evaluator.reset()
        print()        

        del(evaluator)

        return


    def test_demo(self):
        print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ unit tests ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")
        print("Modified unit tests:")
        unittest.main(exit=False)
        print()
        return


class NotRepl:
    '''
    Implements a naive read-evaluate-print loop.
    '''

    def __init__(self):
        pass


    def loop(self):
        calc = Calculator()
        print(Messages().greeting())
        while True:
            ui = input('!$ ')
            if ui.lower() in ['halt', 'stop', 'exit', 'quit', ':q']:
                print("goodbye!")
                break
            if ui.lower() in ['help', 'helpme']:
                self.helpme()
                continue
            calc.noteval(ui, verbose='result')
        del(calc)
        return


    def helpme(self):
        print("valid operators:")
        for n, op in enumerate(Operators.all_ops_kwds):
            print(f" {op}", end=' ')
            if n == 12 or n == 24:
                print()
        print()
        print("All operators and variables must be separated by spaces,\n  except for the following: ( ) ! ~ , ^")
        print("Parentheses are valid for arbitrary nesting depth,\n  but this is not exhaustively tested!")
        print("Braces and brackets are not valid.")
        print("ANS is the only available keyword, and is only available in this REPL. It returns the")
        print("previous answer to the next expression: e.g., !$ ANS + 3")
        print("LOG function is of the form LOG(exponent, base) and requires a base")
        print("Any numerical expression that produces a boolean can be mixed with all boolean operators;")
        print("but again, this is not exhaustively tested.")
        print("Have fun calculating!")
        return


class Messages:
    def __init__(self):

        self.notrepldemo = [
f"                     ________________________________________________\n",
f"                    /                                                \\\n",
f"                   |    __________________________________________    |\n",
f"                   |   |                                          |   |\n",
f"                   |   |  !$ Welcome to the Calculator REPL !!    |   |\n",
f"                   |   |                                          |   |\n",
f"                   |   |     To exit, enter one of:               |   |\n",
f"                   |   |     halt  stop  exit  quit  :q           |   |\n",
f"                   |   |                                          |   |\n",
f"                   |   |     To see a list of valid operators,    |   |\n",
f"                   |   |     enter one of:  help  helpme          |   |\n",
f"                   |   |                                          |   |\n",
f"                   |   |     Happy calculating!                   |   |\n",
f"                   |   |                                          |   |\n",
f"                   |   |  !$                                      |   |\n",
f"                   |   |                                          |   |\n",
f"                   |   |__________________________________________|   |\n",
f"                   |                                                  |\n",
f"                    \\_________________________________________________/\n",
f"                           \\___________________________________/\n",
f"                        ___________________________________________\n",
f"                     _-'    .-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.  --- `-_\n",
f"                  _-'.-.-. .---.-.-.-.-.-.-.-.-.-.-.-.-.-.-.--.  .-.-.`-_\n",
f"               _-'.-.-.-. .---.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-`__`. .-.-.-.`-_\n",
f"            _-'.-.-.-.-. .-----.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-----. .-.-.-.-.`-_\n",
f"         _-'.-.-.-.-.-. .---.-. .-------------------------. .-.---. .---.-.-.-.`-_\n",
f"        :-------------------------------------------------------------------------:\n",
f"        `---._.-------------------------------------------------------------._.---'\n"]
    def greeting(self):
        return ''.join(self.notrepldemo)


if __name__ == "__main__":
    sys.exit(main())
