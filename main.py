from pycryptosat import Solver
from itertools import combinations, product, count
from datetime import datetime


def generate_crossing_constraints(words, is_in_hor_mode, is_x_coord, is_y_coord, allow_horizontal_word_overlap, allow_vertical_word_overlap):
    def are_compatible(word1: str, word2: str, pos1: int, pos2: int):
        if pos1 > pos2:
            pos1, pos2, word1, word2 = pos2, pos1, word2, word1
        if pos1 <= pos2 < pos1 + len(word1):
            overlap_length = min(len(word1) - pos2 + pos1, len(word2))
            return word1[pos2 - pos1:pos2 - pos1 + overlap_length] == word2[:overlap_length]
        return True

    for (iw1, w1), (iw2, w2) in combinations(enumerate(words), 2):
        if w1 == w2:
            continue

        if is_in_hor_mode[iw1] == is_in_hor_mode[iw2]:
            if is_in_hor_mode[iw1]:
                common_coord, other_coord, allow_overlap = is_y_coord, is_x_coord, allow_horizontal_word_overlap
            else:
                common_coord, other_coord, allow_overlap = is_x_coord, is_y_coord, allow_vertical_word_overlap

            for cc in range(min(len(common_coord[iw1]), len(common_coord[iw2]))):
                vcc1, vcc2 = common_coord[iw1][cc], common_coord[iw2][cc]
                for oc1, voc1 in enumerate(other_coord[iw1]):
                    for oc2 in range(max(0, oc1 - len(w2) + 1), min(len(other_coord[iw2]), oc1 + len(w1))):
                        voc2 = other_coord[iw2][oc2]
                        if not (allow_overlap and are_compatible(w1, w2, oc1, oc2)):
                            yield [-vcc1, -vcc2, -voc1, -voc2]
            continue

        if not is_in_hor_mode[iw1]:
            iw1, w1, iw2, w2 = iw2, w2, iw1, w1
        for (x1, vx1), (y1, vy1) in product(enumerate(is_x_coord[iw1]), enumerate(is_y_coord[iw1])):
            for x2 in range(x1, x1 + len(w1)):
                vx2 = is_x_coord[iw2][x2]
                for y2 in range(max(0, y1 - len(w2) + 1), min(y1 + 1, len(is_y_coord[iw2]))):
                    if w1[x2 - x1] != w2[y1 - y2]:
                        yield [-vx1, -vy1, -vx2, -is_y_coord[iw2][y2]]


def ensure_nonempty_first_row_and_column(is_x_coord, is_y_coord):
    return [
        [var_list[0] for var_list in is_x_coord],
        [var_list[0] for var_list in is_y_coord]
    ]


def ensure_exactly_one_word_placement(words, is_in_hor_mode, is_x_coord, is_y_coord, is_placed):
    for iw in range(len(words)):
        yield [-is_placed[iw]] + is_x_coord[iw]
        yield [-is_placed[iw]] + is_y_coord[iw]

    for (iw1, w1), (iw2, w2) in combinations(enumerate(words), 2):
        if w1 == w2 and is_in_hor_mode[iw1] != is_in_hor_mode[iw2]:
            yield [is_placed[iw1], is_placed[iw2]]
            yield [-is_placed[iw1], -is_placed[iw2]]


def forbid_cells(words, is_in_hor_mode, is_x_coord, is_y_coord, forbidden_cells):
    for (x, y), (iw, w) in product(forbidden_cells, enumerate(words)):
        if is_in_hor_mode[iw]:
            fixed_coord_var, other_coord, other_coord_list = is_y_coord[iw][y], x, is_x_coord[iw]
        else:
            fixed_coord_var, other_coord, other_coord_list = is_x_coord[iw][x], y, is_y_coord[iw]
        for c in range(max(0, other_coord - len(w) + 1), min(other_coord + 1, len(other_coord_list))):
            yield [-other_coord_list[c], -fixed_coord_var]


def make_problem(words, x_bound, y_bound):
    is_in_hor_mode = [True] * len(words) + [False] * len(words)
    words = words + words

    is_x_coord: list[list[int]] = [[] for _ in range(len(words))]
    is_y_coord: list[list[int]] = [[] for _ in range(len(words))]

    clauses = []

    counter = count(1)
    is_placed = []
    for iw in range(len(words)):
        is_placed.append(next(counter))
    for iw, w in enumerate(words):
        for x in range(x_bound + ((1 - len(w)) if is_in_hor_mode[iw] else 0)):
            is_x_coord[iw].append(next(counter))
        for y in range(y_bound + ((1 - len(w)) if not is_in_hor_mode[iw] else 0)):
            is_y_coord[iw].append(next(counter))

    clauses.extend(generate_crossing_constraints(words, is_in_hor_mode, is_x_coord, is_y_coord, True, True))
    clauses.extend(ensure_nonempty_first_row_and_column(is_x_coord, is_y_coord))
    clauses.extend(ensure_exactly_one_word_placement(words, is_in_hor_mode, is_x_coord, is_y_coord, is_placed))
    clauses.extend(forbid_cells(words, is_in_hor_mode, is_x_coord, is_y_coord, [(3, 8), (6, 8), (2, 6)]))
    clauses = list(set(map(tuple, map(sorted, clauses))))
    clauses.sort()
    return clauses, words, is_in_hor_mode, is_placed, is_x_coord, is_y_coord


def solve_problem(clauses, words, is_in_hor_mode, is_placed, is_x_coord, is_y_coord):
    solver = Solver()
    for clause in set(map(tuple, map(sorted, clauses))):
        solver.add_clause(clause)

    sat, solution = solver.solve()
    print('formula is', f'{"" if sat else "un"}satisfiable')

    if not sat:
        return []
    return [
        {
            "word": w,
            "x": next(x for x, vx in enumerate(is_x_coord[iw]) if solution[vx]),
            "y": next(y for y, vy in enumerate(is_y_coord[iw]) if solution[vy]),
            "horizontal": is_in_hor_mode[iw]
        }
        for iw, w in enumerate(words) if solution[is_placed[iw]]
    ]


def print_solution(placement_data, x_bound, y_bound):
    grid = [["·"] * x_bound for _ in range(y_bound)]

    for data in placement_data:
        for i, c in enumerate(data["word"]):
            if data["horizontal"]:
                if grid[data["y"]][data["x"] + i] not in ("·", c):
                    print("Conflict at", data["x"] + i, data["y"])
                grid[data["y"]][data["x"] + i] = c
            else:
                if grid[data["y"] + i][data["x"]] not in ("·", c):
                    print("Conflict at", data["x"], data["y"] + i)
                grid[data["y"] + i][data["x"]] = c

    print("\n".join(" ".join(row) for row in grid))


def main():
    words = [
        "pizza", "cake", "juice", "soda", "burger", "salad", "toast", "fruit", "sushi", "pasta", "milk",
        "corn", "rice", "bean", "chef", "menu", "fork", "spoon", "plate", "bowl", "feast", "taste"
    ]
    x_bound = 10
    y_bound = 10

    stage_1_start = datetime.now()
    print("Generating clauses...")
    clauses, words_ext, is_in_hor_mode, is_placed, is_x_coord, is_y_coord = make_problem(words, x_bound, y_bound)
    stage_2_start = datetime.now()
    print("Clause generation took ", (stage_2_start - stage_1_start).total_seconds(), "s")
    print("Number of clauses: ", len(clauses))
    print("Solving...")
    placement_data = solve_problem(clauses, words_ext, is_in_hor_mode, is_placed, is_x_coord, is_y_coord)
    stage_3_start = datetime.now()
    print("Solving took ", (stage_3_start - stage_2_start).total_seconds(), "s")
    print("Solution:")
    print_solution(placement_data, x_bound, y_bound)


if __name__ == '__main__':
    main()
