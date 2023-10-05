import sys
import re
from z3 import Solver, Int, sat

def handle_error(error_message):
    print(f"Ошибка: {error_message}")
    sys.exit(1)

def validate_input(rule):
    if not re.match(r"^[a-zA-Z0-9_,() -><]+$", rule):
        handle_error("Неверный формат ввода.")

def extract_functions(expression):
    return set(re.findall(r'(\w+)\(', expression))

def extract_variables(expression, functions):
    variables = set(re.findall(r'\b([a-z]+)\b', expression))
    return variables - set(functions)

def construct_interpretation(functions, variables):
    interpretations = {}
    for func in functions:
        coefs = [f"{func}_a{i}" for i in range(len(variables) + 1)]
        interpretations[func] = coefs
    return interpretations

def construct_composition(rules, interpretations):
    compositions = {}
    for rule in rules:
        rule = rule.strip()
        if not rule:
            continue
        left, right = rule.split(" -> ")
        if '(' in left and '(' in right:
            outer_func = left.split('(')[0]
            inner_elements = left.split('(')[1].split(')')[0].split(',')
            composition = '+'.join(interpretations[outer_func])
            for inner_element in inner_elements:
                inner_element = inner_element.strip()
                if inner_element in interpretations:
                    composition += '+' + '+'.join(interpretations[inner_element])
                else:
                    composition += '+' + inner_element
            compositions[left] = composition
    return compositions

def construct_inequalities(compositions):
    inequalities = {}
    for left, right in compositions.items():
        inequalities[left] = right + " >= " + left if ">=" in left else right + " > " + left
    return inequalities

def parse_expression_to_z3(expr, z3_vars, interpretations):
    terms = expr.split('+')
    z3_expr = 0
    for term in terms:
        term = term.strip()
        if term in z3_vars:
            z3_expr += z3_vars[term]
        elif '(' in term:
            func_name = term.split('(')[0]
            z3_expr += sum([z3_vars[coef] for coef in interpretations[func_name]])
        else:
            try:
                z3_expr += int(term)
            except ValueError:
                handle_error(f"Неожиданный элемент: {term}")
    return z3_expr

def verify_solution(model, inequalities, z3_vars, interpretations):
    verification_solver = Solver()
    for left, inequality in inequalities.items():
        left_expr, right_expr = inequality.split(" >= ") if ">=" in inequality else inequality.split(" > ")
        left_z3 = parse_expression_to_z3(left_expr, z3_vars, interpretations)
        right_z3 = parse_expression_to_z3(right_expr, z3_vars, interpretations)
        verification_solver.add(
            model.eval(left_z3) >= model.eval(right_z3)) if ">=" in inequality else verification_solver.add(
            model.eval(left_z3) > model.eval(right_z3))
    return verification_solver.check() == sat

def construct_monotonicity_constraints(functions, variables, interpretations, z3_vars):
    constraints = []
    for func in functions:
        for var1 in variables:
            for var2 in variables:
                if var1 != var2:
                    f_var1 = parse_expression_to_z3(func + "(" + var1 + ")", z3_vars, interpretations)
                    f_var2 = parse_expression_to_z3(func + "(" + var2 + ")", z3_vars, interpretations)
                    constraints.append(f_var1 <= f_var2)
    return constraints

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

    funcs, variables, interpretations, compositions, inequalities = process_rules(example.split("\n"))
    if funcs is None:
        return

    print("\nФункции и их коэффициенты (последний свободный):")
    for func in funcs:
        print(func, interpretations[func])

    print("\nПеременные:")
    print(list(variables))

    print("\nЗапуск Z3 солвера...")
    z3_vars = {}
    for var in variables:
        z3_vars[var] = Int(var)
    for func, coefs in interpretations.items():
        for coef in coefs:
            z3_vars[coef] = Int(coef)

    s = Solver()
    monotonicity_constraints = construct_monotonicity_constraints(funcs, variables, interpretations, z3_vars)
    s.add(monotonicity_constraints)

    for left, inequality in inequalities.items():
        left_expr, right_expr = inequality.split(" >= ") if ">=" in inequality else inequality.split(" > ")
        left_z3 = parse_expression_to_z3(left_expr, z3_vars, interpretations)
        right_z3 = parse_expression_to_z3(right_expr, z3_vars, interpretations)
        s.add(left_z3 >= right_z3) if ">=" in inequality else s.add(left_z3 > right_z3)

    if s.check() == sat:
        model = s.model()
        for d in model.decls():
            print(f"{d.name()} = {model[d]}")
        for coef in z3_vars:
            if model[z3_vars[coef]] is None:
                print(f"{coef} = 0")
        if verify_solution(model, inequalities, z3_vars, interpretations):
            print("Решение корректно!")
        else:
            print("Решение некорректно!")
    else:
        print("Не удается удовлетворить условия")

def process_rules(rules):
    funcs = set()
    variables = set()
    for rule in rules:
        rule = rule.strip()
        if not rule:
            continue
        left, right = rule.split(" -> ")
        funcs.update(extract_functions(left))
        funcs.update(extract_functions(right))
        variables.update(extract_variables(left, funcs))
        variables.update(extract_variables(right, funcs))

    interpretations = construct_interpretation(funcs, variables)
    compositions = construct_composition(rules, interpretations)
    inequalities = construct_inequalities(compositions)
    return funcs, variables, interpretations, compositions, inequalities

if __name__ == "__main__":
    main()
