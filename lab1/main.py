from __future__ import annotations
import re
import sys
from enum import Enum
from collections import namedtuple
import subprocess


ConstructorDict = dict[str, list[list[str]]]
IDENTITY = 'id'

class Constructor:
    cd: ConstructorDict

    def __init__(self, cd: ConstructorDict):
        self.cd = cd

    @staticmethod
    def create_variable(name: str):
        return Constructor(
            {name: [['1']]}
        )

    @staticmethod
    def create_free_coef(value: str):
        return Constructor(
            {IDENTITY: [[value]]}
        )

    def add(self, other: Constructor):
        for var_name, coefs in other.cd.items():
            if var_name in self.cd:
                self.cd[var_name] += other.cd[var_name]
            else:
                self.cd[var_name] = other.cd[var_name]

        return self

    def mul_by_scalar(self, p: str):
        for var_name, coefs in self.cd.items():
            self.cd[var_name] = [cs + [p] for cs in coefs]

    def __repr__(self) -> str:
        return ' + '.join([k + str(v) for k,v in self.cd.items()])

    def get_coef_by_variable(self, name:str):
        if name not in self.cd:
            return '0'
        return  '(+ ' + ' '.join(['(* ' + ' '.join(prod) + ')' for prod in self.cd[name]]) + ')'


class LD(Enum):
    VARSKW = 1
    EQSIGN = 2
    COMMA = 3
    LETTER = 4
    OPEN = 5
    CLOSE = 6
    SKIP = 7
    EOF = 8


LDR = namedtuple('LexDomainRegex', ['regex', 'domain'])
Lexem = namedtuple('Lexem', ['domain', 'value'])


LexDoms = (
            LDR(r'variables', LD.VARSKW),
            LDR(r'\=', LD.EQSIGN),
            LDR(r'\,', LD.COMMA),
            LDR(r'\(', LD.OPEN),
            LDR(r'\)', LD.CLOSE),
            LDR(r'[\s\n\r\t]', LD.SKIP),
            LDR(r'[a-z]', LD.LETTER),
        )


class MyParser:
    lexems: list[Lexem]
    cur: Lexem
    variables: set[str]
    constructors: dict[str, int]
    rules: list[tuple[Constructor, Constructor]]


    def __init__(self, file) -> None:
        string = open(file).read()
        self.lexemize(string)
        self.parse()

    def print_lexems(self):
        print(f'cur: {self.cur}')
        for x in self.lexems:
            print(x)

    def lexemize(self, string):
        self.lexems = []
        while string:
            for ld in LexDoms:
                matched = re.match('^' + ld.regex, string)
                if matched is None:
                    continue
                res = matched[0]
                string = string[len(res):]
                if ld.domain == LD.SKIP:
                    break
                self.lexems.append(Lexem(ld.domain, res))
                break
            else:
                raise RuntimeError(f'parsing Error: {string[:20]}')

        self.lexems.append(Lexem(LD.EOF, '$'))

    def next(self):
        self.cur = self.lexems[0]
        self.lexems = self.lexems[1:]

    def assert_domain(self, domain):
        assert self.cur.domain == domain, f'expected {domain}, got {self.cur.domain}'

    def parse(self):
        self.variables = set()
        self.constructors = dict()
        self.rules = []
        self.next()

        # variables =
        self.assert_domain(LD.VARSKW)
        self.next()

        self.assert_domain(LD.EQSIGN)
        self.next()

        self.assert_domain(LD.LETTER)
        self.variables.add(self.cur.value)
        self.next()

        while self.cur.domain == LD.COMMA:
            self.next()
            self.assert_domain(LD.LETTER)
            self.variables.add(self.cur.value)
            self.next()

        while self.cur.domain == LD.LETTER:
            left = self.parse_constructor()
            self.assert_domain(LD.EQSIGN)
            self.next()
            right = self.parse_constructor()
            self.rules.append((left, right))

        self.assert_domain(LD.EOF)


    def parse_constructor(self) -> Constructor:
        self.assert_domain(LD.LETTER)
        name = self.cur.value
        self.next()

        if name in self.variables:
            return Constructor.create_variable(name)

        args = []
        if self.cur.domain == LD.OPEN:
            self.next()
            args = self.parse_args()
            self.assert_domain(LD.CLOSE)
            self.next()

        if name in self.constructors:
            assert self.constructors[name] == len(args)
        else:
            self.constructors[name] = len(args)

        res = Constructor.create_free_coef(f'{name}{len(args)+1}')
        for i, arg in enumerate(args):
            arg.mul_by_scalar(f'{name}{i+1}')
            res.add(arg)

        return res

    def parse_args(self) -> list[Constructor]:
        args = []
        args.append(self.parse_constructor())
        while self.cur.domain == LD.COMMA:
            self.next()
            args.append(self.parse_constructor())
        return args


class SMTshnik:
    res: str
    mp: MyParser

    def __init__(self, mp) -> None:
        self.mp = mp
        self.res = ''

    def add_str(self, string=''):
        self.res += string + '\n'

    def translate_to_smt(self):
        self.add_str('(set-logic QF_NIA)')
        self.add_str()

        for fname, arity in self.mp.constructors.items():
            for i in range(arity+1):
                self.add_str(f'(declare-const {fname}{i+1} Int)')
                self.add_str(f'(assert (>=  {fname}{i+1} {0 if i == arity else 1}))')
            self.add_str(f'(assert (or {("(and" + " ".join([f"(> {fname}{i+1} 1)" for i in range(arity)]) + ")") if arity > 0 else "" } (> {fname}{arity+1} 0)))')
            self.add_str()
        self.add_str()

        for left, right in self.mp.rules:
            vars = set(left.cd.keys()) | set(right.cd.keys())
            self.add_str('(assert (or ')
            for i in range(2):
                self.add_str('    (and')
                for var in vars:
                    sign = '>' if (var != IDENTITY if i == 1 else var == IDENTITY) else '>='
                    self.add_str(f'        ({sign} {left.get_coef_by_variable(var)} {right.get_coef_by_variable(var)})  ; {var}')
                self.add_str('    )')
            self.add_str('))')

        self.add_str()
        self.add_str('(check-sat)')

    def write(self, file):
        open(file, 'w').write(self.res)


if __name__ == '__main__':
    mp = MyParser(sys.argv[1])
    smt = SMTshnik(mp)
    smt.translate_to_smt()
    smt.write("res.smt2")
    subprocess.run("z3 -smt2 res.smt2".split())
