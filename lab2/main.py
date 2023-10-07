import random
import networkx as nx


def generate_random_regex(alphabet_size, star_height, max_length):
    if max_length == 0:
        return 'ε'  # Пустое регулярное выражение
    else:
        choice = random.choice(['concat', 'alt', 'star', 'lookahead', 'symbol'])

        if choice == 'concat':
            left = generate_random_regex(alphabet_size, star_height,  max_length - 1)
            right = generate_random_regex(alphabet_size, star_height, max_length - len(left))
            return f'({left}{right})'
        elif choice == 'alt':
            left = generate_random_regex(alphabet_size, star_height,  max_length - 1)
            right = generate_random_regex(alphabet_size, star_height,  max_length - len(left))
            return f'({left}|{right})'
        elif choice == 'star':
            inner = generate_random_regex(alphabet_size, star_height - 1,  max_length - 1)
            return f'({inner}*)'
        # elif choice == 'lookahead':
        #     inner = generate_random_regex(alphabet_size, star_height, lookahead_count - 1, max_length - 1)
        #     return f'(?={inner})$'
        else:  # choice == 'symbol'
            return f'({chr(97 + random.randint(0, alphabet_size - 1))})'


def build_reachable_states(regex):
    # Построение графа для определения достижимых состояний
    G = nx.DiGraph()

    def add_states(expr, start_state, final_state):
        if not expr:
            return start_state, final_state
        elif expr[0] == '(':
            # Подвыражение в скобках
            subexpr, rest = find_matching_parenthesis(expr[1:])
            sub_start, sub_final = add_states(subexpr, start_state, final_state)
            return add_states(rest, sub_start, sub_final)
        elif expr[0] == '|':
            # Альтернатива
            left_subexpr, rest = find_matching_pipe(expr[1:])
            left_start, left_final = add_states(left_subexpr, start_state, final_state)
            right_start, right_final = add_states(rest, start_state, final_state)
            G.add_edge(start_state, left_start)
            G.add_edge(start_state, right_start)
            G.add_edge(left_final, final_state)
            G.add_edge(right_final, final_state)
            return start_state, final_state
        elif expr[0] == '*':
            # Итерация
            inner_subexpr, rest = find_matching_star(expr[1:])
            inner_start, inner_final = add_states(inner_subexpr, start_state, final_state)
            G.add_edge(start_state, inner_start)
            G.add_edge(inner_final, inner_start)
            G.add_edge(inner_final, final_state)
            return start_state, final_state
        # elif expr[0] == '?':
        #     # Lookahead
        #     inner_subexpr, rest = find_matching_lookahead(expr[1:])
        #     inner_start, inner_final = add_states(inner_subexpr, start_state, final_state)
        #     G.add_edge(start_state, inner_start)
        #     G.add_edge(inner_final, final_state)
        #     return start_state, final_state
        else:
            # Символы
            symbol = expr[0]
            G.add_edge(start_state, final_state, symbol=symbol)
            return start_state, final_state

    start_state, final_state = add_states(regex, 0, 1)
    return G, start_state, final_state


def find_matching_parenthesis(expr):
    count = 1
    i = 0
    while count > 0:
        i += 1
        if expr[i] == '(':
            count += 1
        elif expr[i] == ')':
            count -= 1
    return expr[:i], expr[i + 1:]


def find_matching_pipe(expr):
    count = 0
    i = 0
    while i < len(expr):
        if expr[i] == '(':
            count += 1
        elif expr[i] == ')':
            count -= 1
        elif expr[i] == '|' and count == 0:
            return expr[:i], expr[i + 1:]
        i += 1
    return expr, ''


def find_matching_star(expr):
    count = 0
    i = 0
    while i < len(expr):
        if expr[i] == '(':
            count += 1
        elif expr[i] == ')':
            count -= 1
        elif expr[i] == '*' and count == 0:
            return expr[:i], expr[i + 1:]
        i += 1
    return expr, ''

#
# def find_matching_lookahead(expr):
#     count = 0
#     i = 0
#     while i < len(expr):
#         if expr[i] == '(':
#             count += 1
#         elif expr[i] == ')':
#             count -= 1
#         elif expr[i] == '?' and count == 0:
#             return expr[:i], expr[i + 1:]
#         i += 1
#     return expr, ''


def bfs(start_state, final_state):
    # Поиск пути BFS в графе
    path = []
    current_state = start_state
    while current_state != final_state:
        next_state = random.choice(list(G.successors(current_state)))
        symbol = G[current_state][next_state]['symbol']
        if symbol:
            path.append(symbol)
        current_state = next_state
    return ''.join(path)


def apply_random_mutations(string):
    # Применение случайных мутаций к строке
    mutations = ['swap', 'permute', 'repeat', 'delete', 'none']
    mutation = random.choice(mutations)
    if mutation == 'swap':
        i, j = random.sample(range(len(string)), 2)
        string = list(string)
        string[i], string[j] = string[j], string[i]
        return ''.join(string)
    elif mutation == 'permute':
        i, j = random.sample(range(len(string)), 2)
        substring = string[i:j]
        substring = random.sample(substring, len(substring))
        return string[:i] + ''.join(substring) + string[j:]
    elif mutation == 'repeat':
        i = random.randint(0, len(string) - 1)
        return string[:i] + random.choice(string[i:]) + string[i:]
    elif mutation == 'delete':
        i = random.randint(0, len(string) - 1)
        return string[:i] + string[i + 1:]
    else:
        return string


def main():
    alphabet_size = 5
    star_height = 3
    # lookahead_count = 2
    max_length = 20

    regex = generate_random_regex(alphabet_size, star_height,  max_length)
    print(f"Случайное регулярное выражение: {regex}")

    G, start_state, final_state = build_reachable_states(regex)

    generated_string = bfs(start_state, final_state)
    print(f"Сгенерированная строка: {generated_string}")

    mutated_string = apply_random_mutations(generated_string)
    print(f"Мутированная строка: {mutated_string}")


# print(generate_random_regex(10, 3, 20))
