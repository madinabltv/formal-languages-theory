import subprocess
import sys
import re
from z3 import *

def handle_error(error_message):
    print(f"Ошибка: {error_message}")
    sys.exit(1)

def validate_input(rule):
    if not re.match(r"^[a-zA-Z0-9_() ->]+$", rule):
        handle_error("Неверный формат ввода.")

def extract_functions(expression):
    """
    Извлекает все имена функций из выражения.
    :param expression: строка, содержащая выражение.
    :return: множество имен функций.
    """
    return set(re.findall(r'(\w+)\(', expression))

def extract_variables(expression):
    """
    Извлекает все переменные из выражения.
    :param expression: строка, содержащая выражение.
    :return: множество переменных.
    """
    return set(re.findall(r'\b([a-z]+)\b', expression))

def construct_interpretation(functions, variables):
    """
    Создает словарь для интерпретации функций.
    :param functions: множество имен функций.
    :param variables: множество переменных.
    :return: словарь интерпретаций.
    """
    interpretations = {}
    for func in functions:
        coefs = [f"a{i}" for i in range(len(variables) + 1)]
        interpretations[func] = coefs
    return interpretations

def construct_composition(rules, interpretations):
    """
    Создает словарь для композиций функций.
    :param rules: список правил.
    :param interpretations: словарь интерпретаций.
    :return: словарь композиций.
    """
    compositions = {}
    for rule in rules:
        rule = rule.strip()
        if not rule:
            continue
        left, right = rule.split(" -> ")
        if '(' in left and '(' in right:
            outer_func = left.split('(')[0]
            inner_func = left.split('(')[1].split(')')[0]
            composition = '+'.join(interpretations[outer_func]) + '+' + '+'.join(interpretations[inner_func])
            compositions[left] = composition
    return compositions

def construct_inequalities(compositions):
    """
    Создает словарь для неравенств.
    :param compositions: словарь композиций.
    :return: словарь неравенств.
    """
    inequalities = {}
    for left, right in compositions.items():
        inequalities[left] = right + " >= " + left
    return inequalities

def generate_smt2_spec(inequalities, variables):
    """
    Генерирует SMT2-спецификацию для каждого неравенства.
    :param inequalities: словарь неравенств.
    :param variables: множество переменных.
    :return: строка SMT2-спецификации.
    """
    smt2_spec = ""
    for left, inequality in inequalities.items():
        smt2_spec += f"(assert {inequality})\n"
    smt2_spec += "(check-sat)\n"
    return smt2_spec

def main():
    print("Пример ввода: f(g(x, y)) -> g(x, y)")
    print("Когда поступает пустая строка, ввод считается завершенным")

    example = ""
    while True:
        try:
            line = input()
            if line == "":
                break
            validate_input(line)
            example += line + "\n"
        except EOFError:
            break

    funcs, variables, interpretations, compositions, inequalities, smt2_spec = process_rules(example.split("\n"))
    if funcs is None:
        return
    print("\nФункции и их коэффициенты:")
    for func in funcs:
        print(func, interpretations[func])
    print("\nПеременные:")
    print(list(variables))
    print("\nЗапуск Z3 солвера...")
    try:
        result = subprocess.run(["z3", "-in"], input=smt2_spec, text=True, capture_output=True)
        print(result.stdout)
    except Exception as e:
        print("Ошибка при запуске Z3:", e)

def process_rules(rules):
    funcs = set()
    variables = set()

    for idx, rule in enumerate(rules):
        rule = rule.strip()
        if not rule:
            continue
        if '->' not in rule:
            print(f"Ошибка в строке {idx + 1}: {rule}. Ожидается символ '->'.")
            return None, None, None, None, None, None
        left, right = rule.split(" -> ")
        funcs.update(extract_functions(left))
        funcs.update(extract_functions(right))
        variables.update(extract_variables(left))
        variables.update(extract_variables(right))

    interpretations = construct_interpretation(funcs, variables)
    compositions = construct_composition(rules, interpretations)
    inequalities = construct_inequalities(compositions)
    smt2_spec = generate_smt2_spec(inequalities, variables)

    return funcs, variables, interpretations, compositions, inequalities, smt2_spec

if __name__ == "__main__":
    main()
