import json
from datetime import datetime
from enum import Enum
from itertools import combinations, product
from typing import Iterable
from pydantic import BaseModel
from math import floor, ceil

from pathlib import Path

import pysat.card as PysatCard
from pysat.formula import IDPool
from pysat.solvers import Mergesat3 as SatSolver


class WordPlacement(BaseModel):
    word: str
    x: int
    y: int
    horizontal: bool


class IntersectionType(Enum):
    CROSSING = 0
    HORIZONTAL_OVERLAP = 1
    VERTICAL_OVERLAP = 2


def generate_crossing_constraints(
        words, is_in_hor_mode, is_x_coord, is_y_coord,
        allowed_intersections: Iterable[IntersectionType] = None,
        register_intersections: bool = False,
        vpool: IDPool = None):
    if register_intersections and vpool is None:
        raise ValueError("vpool must be provided if register_intersections is True")
    if allowed_intersections is None:
        allowed_intersections = set()
    allow_horizontal_overlaps = IntersectionType.HORIZONTAL_OVERLAP in allowed_intersections
    allow_vertical_overlaps = IntersectionType.VERTICAL_OVERLAP in allowed_intersections
    allow_crossings = IntersectionType.CROSSING in allowed_intersections

    clause_list = []
    intersections_per_word = [[] for _ in words]

    for (iw1, w1), (iw2, w2) in combinations(enumerate(words), 2):
        if w1 == w2:
            continue

        if is_in_hor_mode[iw1] == is_in_hor_mode[iw2]:
            if is_in_hor_mode[iw1]:
                common_coord, other_coord, allow_overlap = is_y_coord, is_x_coord, allow_horizontal_overlaps
            else:
                common_coord, other_coord, allow_overlap = is_x_coord, is_y_coord, allow_vertical_overlaps

            d = max(len(w1), len(w2))
            are_compatible = [True] * (2 * d)
            for shift in range(1 - len(w2), 0):
                overlap_length = min(len(w2) + shift, len(w1))
                are_compatible[shift + d] = w2[-shift:overlap_length - shift] == w1[:overlap_length]
            for shift in range(0, len(w1)):
                overlap_length = min(len(w1) - shift, len(w2))
                are_compatible[shift + d] = w1[shift:shift + overlap_length] == w2[:overlap_length]

            for cc in range(min(len(common_coord[iw1]), len(common_coord[iw2]))):
                vcc1, vcc2 = common_coord[iw1][cc], common_coord[iw2][cc]
                for oc1, voc1 in enumerate(other_coord[iw1]):
                    for oc2 in range(max(0, oc1 - len(w2) + 1), min(len(other_coord[iw2]), oc1 + len(w1))):
                        voc2 = other_coord[iw2][oc2]

                        if not (allow_overlap and are_compatible[oc2 - oc1 + d]):
                            clause_list.append([-vcc1, -vcc2, -voc1, -voc2])
                        elif register_intersections:
                            new_var = vpool.id()
                            clause_list.extend([
                                [new_var, -vcc1, -vcc2, -voc1, -voc2],
                                [-new_var, vcc1], [-new_var, vcc2], [-new_var, voc1], [-new_var, voc2]
                            ])
                            intersections_per_word[iw1].append(new_var)
                            intersections_per_word[iw2].append(new_var)
            continue

        if not is_in_hor_mode[iw1]:
            iw1, w1, iw2, w2 = iw2, w2, iw1, w1
        for x1, vx1 in enumerate(is_x_coord[iw1]):
            for x2 in range(x1, x1 + len(w1)):
                vx2 = is_x_coord[iw2][x2]
                for y1, vy1 in enumerate(is_y_coord[iw1]):
                    for y2 in range(max(0, y1 - len(w2) + 1), min(y1 + 1, len(is_y_coord[iw2]))):
                        vy2 = is_y_coord[iw2][y2]
                        if not (allow_crossings and w1[x2 - x1] == w2[y1 - y2]):
                            clause_list.append([-vx1, -vy1, -vx2, -vy2])
                        elif register_intersections:
                            new_var = vpool.id()
                            clause_list.extend([
                                [new_var, -vx1, -vy1, -vx2, -vy2],
                                [-new_var, vx1], [-new_var, vy1], [-new_var, vx2], [-new_var, vy2]
                            ])
                            intersections_per_word[iw1].append(new_var)
                            intersections_per_word[iw2].append(new_var)
    return clause_list, intersections_per_word


def ensure_nonempty_first_row_and_column(is_x_coord, is_y_coord):
    return [
        [var_list[0] for var_list in is_x_coord],
        [var_list[0] for var_list in is_y_coord]
    ]


def ensure_exactly_one_word_placement(words, is_in_hor_mode, is_x_coord, is_y_coord, is_placed):
    for iw in range(len(words)):
        for varlist in (is_x_coord[iw], is_y_coord[iw]):
            yield [-is_placed[iw]] + varlist
            for var in varlist:
                yield [is_placed[iw], -var]
            for var1, var2 in combinations(varlist, 2):
                yield [-var1, -var2]

    for (iw1, w1), (iw2, w2) in combinations(enumerate(words), 2):
        if w1 == w2 and is_in_hor_mode[iw1] != is_in_hor_mode[iw2]:
            yield [is_placed[iw1], is_placed[iw2]]
            yield [-is_placed[iw1], -is_placed[iw2]]


def forbid_cells(words, is_in_hor_mode, is_x_coord, is_y_coord, forbidden_cells: list[tuple[int, int]]):
    for (x, y), (iw, w) in product(forbidden_cells, enumerate(words)):
        if is_in_hor_mode[iw]:
            fixed_coord_var, other_coord, other_coord_list = is_y_coord[iw][y], x, is_x_coord[iw]
        else:
            fixed_coord_var, other_coord, other_coord_list = is_x_coord[iw][x], y, is_y_coord[iw]
        for c in range(max(0, other_coord - len(w) + 1), min(other_coord + 1, len(other_coord_list))):
            yield [-other_coord_list[c], -fixed_coord_var]


def bound_isolated_component_size(words, intersections_per_word, min_component_size):
    n_unique_words = len(words) // 2
    intersections_per_word = [set(lits) | set(intersections_per_word[iw + n_unique_words]) for iw, lits in
                              enumerate(intersections_per_word[:n_unique_words])]

    pairwise_intersection_vars = [[set() for _ in range(n_unique_words)] for __ in range(n_unique_words)]
    for iw1, iw2 in combinations(range(n_unique_words), 2):
        pairwise_intersection_vars[iw1][iw2] = intersections_per_word[iw1] & intersections_per_word[iw2]
        pairwise_intersection_vars[iw2][iw1] = pairwise_intersection_vars[iw1][iw2]

    all_word_indices = set(range(n_unique_words))

    for component_size in range(1, min_component_size):
        for component in combinations(all_word_indices, component_size):
            clause = []
            for iw1, iw2 in product(component, all_word_indices - set(component)):
                clause.extend(pairwise_intersection_vars[iw1][iw2])
            yield clause


def forbid_placement(words, is_in_hor_mode, is_x_coord, is_y_coord, is_placed,
                     forbidden_placements: list[WordPlacement]):
    clause = []
    for iw, (w, h) in enumerate(zip(words, is_in_hor_mode)):
        if word_data := next((data for data in forbidden_placements if data.word == w and data.horizontal == h), None):
            clause.extend([-is_placed[iw], -is_x_coord[iw][word_data.x], -is_y_coord[iw][word_data.y]])
    return clause


class IntersectionOptions(BaseModel):
    intersections_bound: int
    qty_bound: int


class CrosswordOptions(BaseModel):
    max_skewness: float = None
    min_isolated_component_size: int = 2
    min_words_with_many_intersections: IntersectionOptions = None
    forbidden_cells: list[tuple[int, int]] = []
    forbidden_placements: list[WordPlacement] = []


def make_problem(
        words,
        x_bound,
        y_bound,
        options: CrosswordOptions = None
):
    if options is None:
        options = CrosswordOptions()
    n_original_words = len(words)
    is_in_hor_mode = [True] * len(words) + [False] * len(words)
    words = words + words

    is_x_coord: list[list[int]] = [[] for _ in range(len(words))]
    is_y_coord: list[list[int]] = [[] for _ in range(len(words))]

    clauses = []

    id_pool = IDPool()
    is_placed = []
    for iw in range(len(words)):
        is_placed.append(id_pool.id())
    for iw, w in enumerate(words):
        for x in range(x_bound + ((1 - len(w)) if is_in_hor_mode[iw] else 0)):
            is_x_coord[iw].append(id_pool.id())
        for y in range(y_bound + ((1 - len(w)) if not is_in_hor_mode[iw] else 0)):
            is_y_coord[iw].append(id_pool.id())

    if options.max_skewness is not None:
        assert 0. < options.max_skewness <= 1.
        clauses.extend(PysatCard.CardEnc.atleast(
            lits=is_placed[:n_original_words],
            bound=floor(n_original_words * (1 - options.max_skewness) * 0.5),
            encoding=PysatCard.EncType.seqcounter,
            vpool=id_pool).clauses
                       )
        clauses.extend(PysatCard.CardEnc.atmost(
            lits=is_placed[:n_original_words],
            bound=ceil(n_original_words * (1 + options.max_skewness) * 0.5),
            encoding=PysatCard.EncType.seqcounter,
            vpool=id_pool).clauses
                       )

    clause_list, intersection_vars = generate_crossing_constraints(
        words, is_in_hor_mode, is_x_coord, is_y_coord,
        allowed_intersections=[IntersectionType.CROSSING, IntersectionType.HORIZONTAL_OVERLAP,
                               IntersectionType.VERTICAL_OVERLAP],
        register_intersections=True,
        vpool=id_pool
    )
    clauses.extend(clause_list)

    if options.min_isolated_component_size == 2:
        for i, lits in enumerate(intersection_vars):
            clauses.append(list(lits) + [-is_placed[i]])
    elif options.min_isolated_component_size > 2:
        min_isolated_component_size = min(options.min_isolated_component_size, (n_original_words + 1) // 2)
        clauses.extend(bound_isolated_component_size(words, intersection_vars, min_isolated_component_size))

    if options.min_words_with_many_intersections is not None:
        new_vars = [id_pool.id() for _ in words]
        clauses.extend(
            clause + [-new_vars[iw]]
            for iw, lits in enumerate(intersection_vars)
            for clause in
            PysatCard.CardEnc.atleast(lits=lits, bound=options.min_words_with_many_intersections.intersections_bound,
                                      encoding=PysatCard.EncType.seqcounter, vpool=id_pool).clauses
        )
        clauses.extend(
            PysatCard.CardEnc.atleast(lits=new_vars, bound=options.min_words_with_many_intersections.qty_bound,
                                      encoding=PysatCard.EncType.seqcounter, vpool=id_pool).clauses
        )

    clauses.extend(ensure_nonempty_first_row_and_column(is_x_coord, is_y_coord))
    clauses.extend(ensure_exactly_one_word_placement(words, is_in_hor_mode, is_x_coord, is_y_coord, is_placed))
    clauses.extend(forbid_cells(words, is_in_hor_mode, is_x_coord, is_y_coord, options.forbidden_cells))
    clauses.extend(
        forbid_placement(words, is_in_hor_mode, is_x_coord, is_y_coord, is_placed, options.forbidden_placements))
    print("Sorting and deduplicating...")
    return list(set(map(tuple, map(sorted, clauses)))), words, is_in_hor_mode, is_placed, is_x_coord, is_y_coord


def solve_problem(clauses, words, is_in_hor_mode, is_placed, is_x_coord, is_y_coord):
    with SatSolver() as solver:
        for clause in clauses:
            solver.add_clause(clause)

        if not solver.solve():
            return []

        model = solver.get_model()
        return [
            WordPlacement(
                word=w,
                x=next(x for x, vx in enumerate(is_x_coord[iw]) if vx in model),
                y=next(y for y, vy in enumerate(is_y_coord[iw]) if vy in model),
                horizontal=is_in_hor_mode[iw]
            )
            for iw, w in enumerate(words) if is_placed[iw] in model
        ]


def print_solution(placement_data: list[WordPlacement], x_bound, y_bound):
    grid = [["·"] * x_bound for _ in range(y_bound)]

    for data in placement_data:
        for i, c in enumerate(data.word):
            if data.horizontal:
                if grid[data.y][data.x + i] not in ("·", c):
                    print("Conflict at", data.x + i, data.y)
                grid[data.y][data.x + i] = c
            else:
                if grid[data.y + i][data.x] not in ("·", c):
                    print("Conflict at", data.x, data.y + i)
                grid[data.y + i][data.x] = c

    print("\n".join(" ".join(row) for row in grid))


def print_dimacs(clauses):
    n_clauses = len(clauses)
    n_vars = max(map(abs, (lit for clause in clauses for lit in clause)))
    print("p cnf 1000", len(clauses))
    with open("output.cnf", "w") as f:
        f.write(f"p cnf {n_vars} {n_clauses}\n")
        f.write("\n".join(" ".join(str(lit) for lit in clause) + " 0" for clause in clauses))


def save_solution(placement_data):
    jsonified = json.dumps([data.dict() for data in placement_data], indent=2)
    Path("output/output.js").write_text(f"var placement_data = {jsonified};")


def main():
    words = [
        "House",
        "Apartment",
        "Park",
        "School",
        "Street",
        "Store",
        "Bus",
        "Car",
        "Tree",
        "Garden",
        "Kitchen",
        "Bedroom",
        "Bathroom",
        "Playground",
        "Library",
        "Restaurant",
        "Supermarket",
        "Bridge",
        "Museum",
        "Traffic"
    ]
    words = [w.lower() for w in words]

    # words = [
    #     "elephant", "giraffe", "tiger", "zebra", "kangaroo", "penguin", "lion", "monkey", "bear", "rabbit", "ant", "rat", "bee",
    #     "turtle", "frog", "duck", "fish", "shark", "whale", "dolphin", "octopus", "butterfly", "swan", "eagle", "owl", "parrot", "bat"
    # ]

    x_bound = 11
    y_bound = 11
    # var placement_data = [{"word": "cake", "x": 6, "y": 9, "horizontal": true}, {"word": "soda", "x": 4, "y": 4, "horizontal": true}, {"word": "salad", "x": 1, "y": 7, "horizontal": true}, {"word": "sushi", "x": 4, "y": 3, "horizontal": true}, {"word": "pasta", "x": 1, "y": 9, "horizontal": true}, {"word": "corn", "x": 3, "y": 6, "horizontal": true}, {"word": "bean", "x": 0, "y": 4, "horizontal": true}, {"word": "chef", "x": 5, "y": 0, "horizontal": true}, {"word": "menu", "x": 5, "y": 2, "horizontal": true}, {"word": "plate", "x": 3, "y": 1, "horizontal": true}, {"word": "feast", "x": 0, "y": 5, "horizontal": true}, {"word": "taste", "x": 2, "y": 8, "horizontal": true}, {"word": "table", "x": 5, "y": 5, "horizontal": true}, {"word": "pizza", "x": 2, "y": 0, "horizontal": false}, {"word": "juice", "x": 1, "y": 0, "horizontal": false}, {"word": "burger", "x": 9, "y": 1, "horizontal": false}, {"word": "toast", "x": 4, "y": 5, "horizontal": false}, {"word": "fruit", "x": 8, "y": 0, "horizontal": false}, {"word": "milk", "x": 8, "y": 6, "horizontal": false}, {"word": "rice", "x": 9, "y": 6, "horizontal": false}, {"word": "fork", "x": 0, "y": 5, "horizontal": false}, {"word": "spoon", "x": 3, "y": 0, "horizontal": false}, {"word": "bowl", "x": 7, "y": 5, "horizontal": false}, {"word": "glass", "x": 4, "y": 0, "horizontal": false}];
    # var placement_data = [{"word": "elephant", "x": 1, "y": 11, "horizontal": true}, {"word": "giraffe", "x": 1, "y": 1, "horizontal": true}, {"word": "tiger", "x": 1, "y": 8, "horizontal": true}, {"word": "bear", "x": 1, "y": 9, "horizontal": true}, {"word": "rabbit", "x": 4, "y": 9, "horizontal": true}, {"word": "ant", "x": 6, "y": 11, "horizontal": true}, {"word": "frog", "x": 7, "y": 3, "horizontal": true}, {"word": "duck", "x": 8, "y": 8, "horizontal": true}, {"word": "whale", "x": 1, "y": 4, "horizontal": true}, {"word": "dolphin", "x": 0, "y": 0, "horizontal": true}, {"word": "butterfly", "x": 2, "y": 10, "horizontal": true}, {"word": "eagle", "x": 1, "y": 7, "horizontal": true}, {"word": "parrot", "x": 0, "y": 5, "horizontal": true}, {"word": "bat", "x": 4, "y": 3, "horizontal": true}, {"word": "zebra", "x": 8, "y": 0, "horizontal": false}, {"word": "kangaroo", "x": 10, "y": 0, "horizontal": false}, {"word": "penguin", "x": 0, "y": 5, "horizontal": false}, {"word": "lion", "x": 2, "y": 0, "horizontal": false}, {"word": "monkey", "x": 11, "y": 5, "horizontal": false}, {"word": "rat", "x": 5, "y": 8, "horizontal": false}, {"word": "bee", "x": 1, "y": 9, "horizontal": false}, {"word": "turtle", "x": 6, "y": 3, "horizontal": false}, {"word": "fish", "x": 7, "y": 3, "horizontal": false}, {"word": "shark", "x": 3, "y": 2, "horizontal": false}, {"word": "octopus", "x": 9, "y": 0, "horizontal": false}, {"word": "swan", "x": 1, "y": 3, "horizontal": false}, {"word": "owl", "x": 4, "y": 5, "horizontal": false}];
    # var placement_data = [{"word": "street", "x": 5, "y": 10, "horizontal": true}, {"word": "bus", "x": 3, "y": 10, "horizontal": true}, {"word": "tree", "x": 6, "y": 10, "horizontal": true}, {"word": "garden", "x": 0, "y": 4, "horizontal": true}, {"word": "kitchen", "x": 0, "y": 1, "horizontal": true}, {"word": "bedroom", "x": 3, "y": 6, "horizontal": true}, {"word": "bathroom", "x": 1, "y": 2, "horizontal": true}, {"word": "playground", "x": 0, "y": 0, "horizontal": true}, {"word": "restaurant", "x": 0, "y": 9, "horizontal": true}, {"word": "bridge", "x": 0, "y": 5, "horizontal": true}, {"word": "museum", "x": 1, "y": 8, "horizontal": true}, {"word": "traffic", "x": 0, "y": 3, "horizontal": true}, {"word": "house", "x": 2, "y": 6, "horizontal": false}, {"word": "apartment", "x": 9, "y": 1, "horizontal": false}, {"word": "park", "x": 0, "y": 7, "horizontal": false}, {"word": "school", "x": 7, "y": 3, "horizontal": false}, {"word": "store", "x": 8, "y": 4, "horizontal": false}, {"word": "car", "x": 6, "y": 3, "horizontal": false}, {"word": "library", "x": 1, "y": 0, "horizontal": false}, {"word": "supermarket", "x": 10, "y": 0, "horizontal": false}];

    stage_1_start = datetime.now()
    print("Generating clauses...")
    clauses, words_extended, is_in_hor_mode, is_placed, is_x_coord, is_y_coord = make_problem(words, x_bound, y_bound)
    stage_2_start = datetime.now()
    print("Clause generation took ", (stage_2_start - stage_1_start).total_seconds(), "s")
    print("Number of clauses: ", len(clauses))
    # print_dimacs(clauses)

    print("Solving...")
    placement_data = solve_problem(clauses, words_extended, is_in_hor_mode, is_placed, is_x_coord, is_y_coord)
    stage_3_start = datetime.now()
    print("Solving took ", (stage_3_start - stage_2_start).total_seconds(), "s")
    print("Solution:")
    print_solution(placement_data, x_bound, y_bound)
    save_solution(placement_data)


if __name__ == '__main__':
    main()
