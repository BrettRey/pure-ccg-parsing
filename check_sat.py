"""Replay the binary queue reduction against a general pure CCG chart."""
from itertools import combinations, product

from check_clique import fwd, recognizes


def build_sat(num_vars, clauses):
    """Return the lexical alternatives at each position, the goal, and the cap."""
    phase = 0
    marker = 0
    bits = ("B0", "B1")

    def head(time, flag):
        return f"H{time}.{int(flag)}"

    def tail(time):
        return f"P{time}"

    words = [{fwd(head(phase, False), tail(marker))}]
    for _ in range(num_vars):
        words.append({fwd(tail(marker), bit, tail(marker + 1)) for bit in bits})
        marker += 1

    for clause in clauses:
        for variable in range(1, num_vars + 1):
            for value, bit in enumerate(bits):
                choices = {fwd(tail(marker), bits[1 - value], tail(marker + 1))}
                literal = variable if value else -variable
                for old_flag in (False, True):
                    new_flag = old_flag or literal in clause
                    if variable == num_vars:
                        if not new_flag:
                            continue
                        new_flag = False
                    choices.add((head(phase + 1, new_flag), "\\", fwd(head(phase, old_flag), bit)))
                words.append(choices)
            phase += 1
            marker += 1

    for _ in range(num_vars):
        words.append({(head(phase + 1, False), "\\", fwd(head(phase, False), bit)) for bit in bits})
        phase += 1
    words.append({tail(marker)})
    return words, head(phase, False), num_vars + 2


def powerset(items):
    return (group for size in range(len(items) + 1) for group in combinations(items, size))


def compare(num_vars, formulas):
    counts = [0, 0]
    for clauses in formulas:
        satisfiable = any(
            all(any(bits[abs(lit) - 1] == (lit > 0) for lit in clause) for clause in clauses)
            for bits in product((False, True), repeat=num_vars)
        )
        words, goal, cap = build_sat(num_vars, clauses)
        for substitution in (False, True):
            if recognizes(words, goal, cap, substitution=substitution) != satisfiable:
                raise AssertionError((clauses, satisfiable, substitution))
        counts[satisfiable] += 1
    return counts


if __name__ == "__main__":
    units = ((1,), (-1,), (2,), (-2,))
    binary = tuple(product((1, -1), (2, -2)))
    ternary = tuple(product((1, -1), (2, -2), (3, -3)))
    for variables, clauses in [(2, units + binary), (3, ternary)]:
        no, yes = compare(variables, powerset(clauses))
        print(f"{variables} variables, {no} UNSAT and {yes} SAT, both rule inventories passed")
