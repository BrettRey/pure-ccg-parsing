"""Exhaustive finite checks of the clique reduction with a general pure CCG chart.

Run "python3 check_clique.py" to enumerate all simple labelled graphs on 1–4
vertices. Each position in lexical_choices represents its own terminal.
"""

import argparse
from collections import defaultdict
from functools import lru_cache
from itertools import combinations


def fwd(result, *arguments):
    for argument in arguments:
        result = (result, "/", argument)
    return result


@lru_cache(maxsize=131072)
def _append(result, suffix):
    for slash, argument in suffix:
        result = (result, slash, argument)
    return result


class _Span:
    """Index a completed chart cell by the two tests in the CCG rule schemas."""

    def __init__(self, categories, degree, substitution):
        self.forward = defaultdict(set)
        self.backward = defaultdict(set)
        self.secondary = defaultdict(set)
        for category in categories:
            if not isinstance(category, str):
                before, slash, arg = category
                primary = self.forward if slash == "/" else self.backward
                primary[(arg, None)].add(before)
                if substitution and not isinstance(before, str):
                    base, inner_slash, demand = before
                    primary = self.forward if inner_slash == "/" else self.backward
                    primary[(demand, (slash, arg))].add(base)

            prefix, suffix = category, ()
            while True:
                self.secondary[(prefix, None)].add(suffix)
                if substitution and suffix:
                    self.secondary[(prefix, suffix[0])].add(suffix)
                if len(suffix) == degree or isinstance(prefix, str):
                    break
                prefix, slash, argument = prefix
                suffix = ((slash, argument),) + suffix


def _join(primary, secondary, produced):
    # A composition key is (Y, None). A substitution key is (Y, shared).
    # Every pair matching one key instantiates that rule.
    smaller = primary if len(primary) < len(secondary) else secondary
    for key in smaller:
        if key in primary and key in secondary:
            for base in primary[key]:
                for suffix in secondary[key]:
                    produced.add(_append(base, suffix))


def recognizes(lexical_choices, goal, degree, *, substitution=True):
    """Exact chart recognition for epsilon-free, bidirectional pure CCG."""
    # ends[j][i] indexes every category for positions i through j-1.
    ends = [{} for _ in range(len(lexical_choices) + 1)]
    if not lexical_choices:
        return False
    for end, choices in enumerate(lexical_choices, start=1):
        open_cells = {end - 1: set(choices)}
        for split in range(end - 1, -1, -1):
            categories = open_cells.pop(split, None)
            if not categories:
                continue
            if end == len(lexical_choices) and split == 0:
                return goal in categories
            right = _Span(categories, degree, substitution)
            ends[end][split] = right
            for start, left in ends[split].items():
                produced = open_cells.setdefault(start, set())
                _join(left.forward, right.secondary, produced)
                _join(right.backward, left.secondary, produced)
    return False


def build_clique(n, edges, k):
    """Return the lexical choices, goal and degree for a k-clique on 1..n."""
    vertices = range(1, n + 1)
    graph = {tuple(sorted(edge)) for edge in edges}

    def cell(vertex):
        return f"v{vertex}"

    def marker(index):
        return f"a{index}"

    def head(stage, memory=None):
        return f"h{stage}:{memory}"

    def read(before, after, vertex):
        return (after, "\\", fwd(before, cell(vertex)))

    stage = 0
    tail = 0
    choices = [{fwd(head(stage), marker(tail))}]
    for _ in range(k):
        choices.append({fwd(marker(tail), cell(v), marker(tail + 1)) for v in vertices})
        tail += 1

    # The queue initially holds k guessed vertices. Each pass rotates all k
    # cells, restoring the original order and checking one pair of positions.
    for first, second in combinations(range(k), 2):
        for slot in range(k):
            for j in range(1, n + 2):
                token = {fwd(marker(tail + j - 1), marker(tail + j))}
                if j > 1:
                    token.add(fwd(marker(tail + j - 2), cell(j - 1), marker(tail + j)))
                if j <= n:
                    memories = vertices if first < slot <= second else [None]
                    for memory in memories:
                        if slot == second and tuple(sorted((memory, j))) not in graph:
                            continue
                        new_memory = j if slot == first else None if slot == second else memory
                        token.add(read(head(stage, memory), head(stage + 1, new_memory), j))
                choices.append(token)
            tail += n + 1
            stage += 1

    for _ in range(k):
        choices.append({read(head(stage), head(stage + 1), v) for v in vertices})
        stage += 1
    choices.append({marker(tail)})
    return choices, head(stage), k + 2


def check_rules():
    # Check both primary positions, both choices of shared slash, and an
    # additional crossed argument beyond the shared one.
    for direction in ("/", "\\"):
        for shared in ("/", "\\"):
            primary = (("X", direction, "Y"), shared, "Z")
            secondary = (("Y", shared, "Z"), "\\", "U")
            expected = (("X", shared, "Z"), "\\", "U")
            words = [(primary,), (secondary,)] if direction == "/" else [(secondary,), (primary,)]
            assert recognizes(words, expected, 2)
            assert not recognizes(words, expected, 1)
            assert not recognizes(words, expected, 2, substitution=False)


def check_graphs(max_vertices):
    cases = 0
    accepted = 0
    for n in range(1, max_vertices + 1):
        vertices = range(1, n + 1)
        pairs = list(combinations(vertices, 2))
        for mask in range(1 << len(pairs)):
            edges = {edge for bit, edge in enumerate(pairs) if mask & (1 << bit)}
            for k in range(1, n + 1):
                expected = any(all(e in edges for e in combinations(subset, 2))
                               for subset in combinations(vertices, k))
                actual = recognizes(*build_clique(n, edges, k))
                if actual != expected:
                    raise AssertionError((n, sorted(edges), k, expected, actual))
                cases += 1
                accepted += actual
    return cases, accepted


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-vertices", type=int, default=4)
    args = parser.parse_args()
    check_rules()
    cases, accepted = check_graphs(args.max_vertices)
    print(f"{cases} graph/clique-size cases passed ({accepted} yes, {cases-accepted} no).")
