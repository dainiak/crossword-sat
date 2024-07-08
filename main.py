import dataclasses
import json
from datetime import datetime
from enum import IntEnum
from itertools import combinations, product
from math import floor, ceil
from pathlib import Path
from typing import Any, Iterable

import pysat.card as pysat_card
from pysat.formula import IDPool
from pysat.solvers import Mergesat3
from pysat.solvers import Glucose4
from pysat.solvers import MinisatGH
from pysat.solvers import CryptoMinisat
from pysat.solvers import Lingeling
from pysat.solvers import MapleChrono, MapleCM


class IntersectionType(IntEnum):
    CROSSING = 0
    HORIZONTAL_OVERLAP = 1
    VERTICAL_OVERLAP = 2


@dataclasses.dataclass
class WordPlacement:
    word: str
    x: int
    y: int
    horizontal: bool


@dataclasses.dataclass
class IntersectionOptions:
    intersections_bound: int
    qty_bound: int


@dataclasses.dataclass
class CrosswordOptions:
    max_skewness: float = None
    min_isolated_component_size: int = 2
    allowed_intersection_types: list[IntersectionType] = None
    min_words_with_many_intersections: IntersectionOptions = None
    forbidden_cells: list[tuple[int, int]] = None
    required_placements: list[WordPlacement] = None
    forbidden_placements: list[WordPlacement] = None
    required_crossings: list[tuple[str, str]] = None
    forbidden_crossings: list[tuple[str, str]] = None

    def __post_init__(self):
        if self.forbidden_placements:
            self.forbidden_placements = [WordPlacement(**data) if isinstance(data, dict) else data for data in self.forbidden_placements]
        if self.required_placements:
            self.required_placements = [WordPlacement(**data) if isinstance(data, dict) else data for data in self.required_placements]
        if isinstance(self.min_words_with_many_intersections, dict):
            self.min_words_with_many_intersections = IntersectionOptions(**self.min_words_with_many_intersections)


class EnhancedJSONEncoder(json.JSONEncoder):
    def default(self, obj):
        if dataclasses.is_dataclass(obj):
            return dataclasses.asdict(obj)
        return super().default(obj)


def generate_crossing_constraints(
        words, is_in_hor_mode, is_x_coord, is_y_coord,
        allowed_intersection_types: Iterable[IntersectionType] = None,
        forbidden_crossings: list[tuple[str, str]] = None,
        register_intersections: bool = False,
        vpool: IDPool = None):
    if register_intersections and vpool is None:
        raise ValueError("vpool must be provided if register_intersections is True")
    if allowed_intersection_types is None:
        allowed_intersection_types = set()
    allow_horizontal_overlaps = IntersectionType.HORIZONTAL_OVERLAP in allowed_intersection_types
    allow_vertical_overlaps = IntersectionType.VERTICAL_OVERLAP in allowed_intersection_types
    allow_crossings = IntersectionType.CROSSING in allowed_intersection_types

    forbidden_crossings = set(forbidden_crossings) if forbidden_crossings else set()

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

                        if not (allow_overlap and are_compatible[oc2 - oc1 + d]) or (w1, w2) in forbidden_crossings:
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
                        if not (allow_crossings and w1[x2 - x1] == w2[y1 - y2]) or (w1, w2) in forbidden_crossings:
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


def compatibility_check(w1, is_hor_1, w2, is_hor_2, dx, dy):
    if is_hor_1 == is_hor_2:
        dc, dco = (dx, dy) if is_hor_1 else (dy, dx)
        if dco != 0 or dc <= - len(w1) or dc >= len(w2):
            return True, None
        if dc >= 0:
            dc, w1, w2 = -dc, w2, w1
        return w1[-dc:len(w2) - dc] == w2[:min(len(w2), len(w1) + dc)], (IntersectionType.HORIZONTAL_OVERLAP if is_hor_1 else IntersectionType.VERTICAL_OVERLAP)

    if not is_hor_1:
        dx, dy = dy, dx
    if dy < 0 or dy >= len(w2) or dx > 0 or dx <= -len(w1):
        return True, None
    return w1[-dx] == w2[dy], IntersectionType.CROSSING


def generate_crossing_constraints_alternative(
        words, x_bound, y_bound, possible_placements,
        allowed_intersection_types: Iterable[IntersectionType] = None,
        forbidden_crossings: list[tuple[str, str]] = None,
        pairwise_intersection_vars=None,
        vpool: IDPool = None):
    if pairwise_intersection_vars is not None and vpool is None:
        raise ValueError("vpool must be provided if register_intersections is True")
    if allowed_intersection_types is None:
        allowed_intersection_types = (IntersectionType.HORIZONTAL_OVERLAP, IntersectionType.VERTICAL_OVERLAP, IntersectionType.CROSSING)

    allowed_intersection_types = set(allowed_intersection_types) | {None}
    forbidden_crossings = set(forbidden_crossings) if forbidden_crossings else set()
    registered_intersections = set()

    v_cache = tuple(
        tuple(
            tuple(
                [None] * (y_bound - ((len(w) - 1) if not is_hor else 0))
                for _ in range(x_bound - ((len(w)-1) if is_hor else 0))
            )
            for is_hor in (0, 1)
        )
        for w in words
    )

    for iw in range(len(words)):
        for x, y, is_hor, v in possible_placements[iw]:
            v_cache[iw][is_hor][x][y] = v

    for (iw1, w1), (iw2, w2) in combinations(enumerate(words), 2):
        for is_hor_1, is_hor_2 in product((False, True), repeat=2):
            cache_1 = v_cache[iw1][is_hor_1]
            cache_2 = v_cache[iw2][is_hor_2]

            if is_hor_1 == is_hor_2:
                if is_hor_1:
                    for y in range(y_bound):
                        for x1, x2 in product(range(x_bound - len(w1) + 1), range(x_bound - len(w2) + 1)):
                            are_compatible, intersection_type = compatibility_check(w1, is_hor_1, w2, is_hor_2, x1 - x2, 0)
                            if not are_compatible or intersection_type not in allowed_intersection_types or intersection_type is not None and (w1, w2) in forbidden_crossings:
                                yield [-cache_1[x1][y], -cache_2[x2][y]]
                            elif are_compatible and intersection_type is not None and (w1, w2) not in forbidden_crossings and pairwise_intersection_vars is not None:
                                new_var = vpool.id()
                                yield from gen_conjunction(new_var, [cache_1[x1][y], cache_2[x2][y]])
                                pairwise_intersection_vars[iw1][iw2].append(new_var)
                else:
                    for x in range(x_bound):
                        for y1, y2 in product(range(y_bound - len(w1) + 1), range(y_bound - len(w2) + 1)):
                            are_compatible, intersection_type = compatibility_check(w1, is_hor_1, w2, is_hor_2, 0, y1 - y2)
                            if not are_compatible or intersection_type not in allowed_intersection_types or intersection_type is not None and (w1, w2) in forbidden_crossings:
                                yield [-cache_1[x][y1], -cache_2[x][y2]]
                            elif are_compatible and intersection_type is not None and (w1, w2) not in forbidden_crossings and pairwise_intersection_vars is not None:
                                new_var = vpool.id()
                                yield from gen_conjunction(new_var, [cache_1[x][y1], cache_2[x][y2]])
                                pairwise_intersection_vars[iw1][iw2].append(new_var)
            else:
                if is_hor_1:
                    for x1, y1 in product(range(x_bound - len(w1) + 1), range(y_bound)):
                        for x2, y2 in product(range(x1, x1 + len(w1)), range(max(0, y1 - len(w2) + 1), min(y1 + 1, y_bound - len(w2) + 1))):
                            are_compatible, intersection_type = compatibility_check(w1, is_hor_1, w2, is_hor_2, x1 - x2, y1 - y2)
                            if not are_compatible or intersection_type not in allowed_intersection_types or intersection_type is not None and (w1, w2) in forbidden_crossings:
                                yield [-cache_1[x1][y1], -cache_2[x2][y2]]
                            elif are_compatible and intersection_type is not None and (w1, w2) not in forbidden_crossings and pairwise_intersection_vars is not None:
                                new_var = vpool.id()
                                yield from gen_conjunction(new_var, [cache_1[x1][y1], cache_2[x2][y2]])
                                pairwise_intersection_vars[iw1][iw2].append(new_var)
                else:
                    for x1, y1 in product(range(x_bound), range(y_bound - len(w1) + 1)):
                        for x2, y2 in product(range(max(0, x1 - len(w2) + 1), min(x1 + 1, x_bound - len(w2) + 1)), range(y1, y1 + len(w1))):
                            are_compatible, intersection_type = compatibility_check(w1, is_hor_1, w2, is_hor_2, x1 - x2, y1 - y2)
                            if not are_compatible or intersection_type not in allowed_intersection_types or intersection_type is not None and (w1, w2) in forbidden_crossings:
                                yield [-cache_1[x1][y1], -cache_2[x2][y2]]
                            elif are_compatible and intersection_type is not None and (w1, w2) not in forbidden_crossings and pairwise_intersection_vars is not None:
                                new_var = vpool.id()
                                yield from gen_conjunction(new_var, [cache_1[x1][y1], cache_2[x2][y2]])
                                pairwise_intersection_vars[iw1][iw2].append(new_var)


def ensure_nonempty_first_row_and_column(is_x_coord, is_y_coord):
    return [
        [var_list[0] for var_list in is_x_coord if var_list],
        [var_list[0] for var_list in is_y_coord if var_list]
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
    if not forbidden_cells:
        return
    for (x, y), (iw, w) in product(forbidden_cells, enumerate(words)):
        if is_in_hor_mode[iw]:
            fixed_coord_var, other_coord, other_coord_list = is_y_coord[iw][y], x, is_x_coord[iw]
        else:
            fixed_coord_var, other_coord, other_coord_list = is_x_coord[iw][x], y, is_y_coord[iw]
        for c in range(max(0, other_coord - len(w) + 1), min(other_coord + 1, len(other_coord_list))):
            yield [-other_coord_list[c], -fixed_coord_var]


def gen_disjunction(target, literals, one_way_implications=False):
    yield [-target, *literals]
    if not one_way_implications:
        yield from ([target, -v] for v in literals)


def gen_conjunction(target, literals):
    yield [target, *(-v for v in literals)]
    yield from ([-target, v] for v in literals)


def gen_uniqueness(literals):
    yield from ([-u, -v] for u, v in combinations(literals, 2))
    yield list(literals)


def bound_isolated_component_size(pairwise_intersection_vars, min_component_size, vpool: IDPool):
    one_way_implications = False
    n_unique_words = len(pairwise_intersection_vars)
    if not min_component_size or min_component_size <= 1 or n_unique_words < 2:
        yield from ()
        return

    min_component_size = min(min_component_size, n_unique_words // 2 + 1)

    if min_component_size == 2:
        yield from ([v for vars in word_var_lists for v in vars] for word_var_lists in pairwise_intersection_vars)
        return

    cumulative_pairwise_intersection_vars: Any = [[None] * n_unique_words for _ in range(n_unique_words)]
    for iw1, iw2 in combinations(range(n_unique_words), 2):
        if not pairwise_intersection_vars[iw1][iw2]:
            continue
        intersection_iw1_iw2 = vpool.id()
        cumulative_pairwise_intersection_vars[iw1][iw2] = intersection_iw1_iw2
        cumulative_pairwise_intersection_vars[iw2][iw1] = intersection_iw1_iw2
        yield from gen_disjunction(intersection_iw1_iw2, pairwise_intersection_vars[iw1][iw2], one_way_implications)

    # ruling out singleton words via constraints on cumulative variables
    for iw1 in range(n_unique_words):
        exists_neighbour_constraint = [
            cumulative_pairwise_intersection_vars[iw1][iw2]
            for iw2 in range(n_unique_words)
            if cumulative_pairwise_intersection_vars[iw1][iw2] is not None
        ]
        if exists_neighbour_constraint:
            yield exists_neighbour_constraint

    # ruling out isolated components of size = 2
    for iw1, iw2 in combinations(range(n_unique_words), 2):
        if cumulative_pairwise_intersection_vars[iw1][iw2] is None:
            continue
        x = [
            cumulative_pairwise_intersection_vars[iw][jw]
            for iw in (iw1, iw2)
            for jw in range(n_unique_words)
            if jw not in (iw1, iw2) and cumulative_pairwise_intersection_vars[iw][jw] is not None
        ]
        if x:
            x.append(-cumulative_pairwise_intersection_vars[iw1][iw2])
            yield x

    # ruling out isolated components of size = 3 or larger, but not in case of total connectivity constraint
    if 4 <= min_component_size <= n_unique_words // 2:
        all_word_indices = set(range(n_unique_words))
        for component_size in range(3, min_component_size):
            for component in combinations(all_word_indices, component_size):
                yield [
                    cumulative_pairwise_intersection_vars[iw1][iw2]
                    for iw1, iw2 in product(component, all_word_indices - set(component))
                    if cumulative_pairwise_intersection_vars[iw1][iw2] is not None
                ]

    if min_component_size <= max(3, n_unique_words // 2):
        return

    # total connectivity case below
    # check if all nodes of the graph are at most max_distance away from the starting_node
    def reachability_constraints(starting_node, max_distance, reachability_flag_var=None):
        nonlocal n_unique_words, cumulative_pairwise_intersection_vars, vpool
        reachability_vars = [[vpool.id() for _ in range(n_unique_words)] for __ in range(max_distance+1)]

        yield [reachability_vars[0][starting_node]]
        yield from ([-reachability_vars[0][node]] for node in range(len(reachability_vars[0])) if node != starting_node)
        yield from ([-reachability_vars[distance][starting_node]] for distance in range(1, max_distance+1))
        if reachability_flag_var is None:
            yield from ([reachability_vars[-1][node]] for node in range(len(reachability_vars[0])) if node != starting_node)
        else:
            yield from gen_conjunction(
                reachability_flag_var,
                [reachability_vars[-1][node] for node in range(len(reachability_vars[0])) if node != starting_node]
            )

        products_ijj: Any = [[[None] * n_unique_words for _ in range(n_unique_words)] for __ in range(max_distance+1)]
        for d in range(1, max_distance+1):
            for i in range(n_unique_words):
                if i == starting_node:
                    continue
                for j in range(n_unique_words):
                    if cumulative_pairwise_intersection_vars[i][j] is None:
                        continue
                    products_ijj[d][i][j] = vpool.id()
                    yield from gen_conjunction(
                        products_ijj[d][i][j],
                        [reachability_vars[d - 1][j], cumulative_pairwise_intersection_vars[i][j]]
                    )
                yield from gen_disjunction(
                    reachability_vars[d][i],
                    [products_ijj[d][i][j] for j in range(n_unique_words) if products_ijj[d][i][j] is not None] + [reachability_vars[d - 1][i]],
                    one_way_implications
                )

    def reachability_2():
        nonlocal vpool, n_unique_words, cumulative_pairwise_intersection_vars, one_way_implications
        reachability_vars = cumulative_pairwise_intersection_vars
        max_distance = n_unique_words - 1
        for stage in range(n_unique_words):
            max_distance = (max_distance + 1) // 2

            reachability_2_vars: Any = [[None] * n_unique_words for _ in range(n_unique_words)]
            for iw1, iw2 in combinations(range(n_unique_words), 2):
                common_neighbours = [reachability_vars[iw1][iw2]] if reachability_vars[iw1][iw2] is not None else []
                for iw in set(range(n_unique_words)) - {iw1, iw2}:
                    if reachability_vars[iw1][iw] is not None and reachability_vars[iw2][iw] is not None:
                        common_neighbours.append(vpool.id())
                        yield from gen_conjunction(
                            common_neighbours[-1],
                            [reachability_vars[iw1][iw], reachability_vars[iw2][iw]]
                        )
                if common_neighbours:
                    if max_distance > 1:
                        reachability_2_vars[iw1][iw2] = vpool.id()
                        reachability_2_vars[iw2][iw1] = reachability_2_vars[iw1][iw2]
                        yield from gen_disjunction(reachability_2_vars[iw1][iw2], common_neighbours, one_way_implications)
                    else:
                        yield common_neighbours

            if max_distance > 1:
                reachability_vars = reachability_2_vars
                continue

            yield from (
                [reachability_2_vars[iw1][iw2]]
                for iw1, iw2 in combinations(range(n_unique_words), 2)
                if reachability_2_vars[iw1][iw2] is not None
            )
            break

    yield from reachability_2()

    # yield from reachability_constraints(node, 4)
    # yield from reachability_constraints(0, n_unique_words - 1)
    #
    # reachability_flag_vars = [vpool.id() for _ in range(n_unique_words)]
    # yield reachability_flag_vars
    # for node in range(0, n_unique_words):
    #     yield from reachability_constraints(node, 4, reachability_flag_vars[node])
    #     yield from reachability_constraints(node, n_unique_words - 1)


def require_placements(words, is_in_hor_mode, is_x_coord, is_y_coord, is_placed,
                       required_placements: list[WordPlacement]):
    if not required_placements:
        return
    for iw, (w, h) in enumerate(zip(words, is_in_hor_mode)):
        for word_data in required_placements:
            if word_data.word == w and word_data.horizontal == h:
                yield [is_placed[iw]]
                if word_data.x is not None:
                    yield [is_x_coord[iw][word_data.x]]
                if word_data.y is not None:
                    yield [is_y_coord[iw][word_data.y]]


def forbid_placements(words, is_in_hor_mode, is_x_coord, is_y_coord, is_placed,
                      forbidden_placements: list[WordPlacement]):
    if not forbidden_placements:
        return
    for iw, (w, h) in enumerate(zip(words, is_in_hor_mode)):
        for word_data in forbidden_placements:
            if word_data.word == w and (word_data.horizontal == h or word_data.horizontal is None):
                if word_data.x is None:
                    if word_data.y is None:
                        yield [-is_placed[iw]]
                    else:
                        yield [-is_placed[iw], -is_y_coord[iw][word_data.y]]
                else:
                    if word_data.y is None:
                        yield [-is_placed[iw], -is_x_coord[iw][word_data.x]]
                    else:
                        yield [-is_placed[iw], -is_x_coord[iw][word_data.x], -is_y_coord[iw][word_data.y]]


def guaranteed_infeasible(words, x_bound, y_bound):
    return (
        x_bound < 1 or y_bound < 1
        or sum(map(len, words)) > 2 * x_bound * y_bound
        or any(len(word) > max(x_bound, y_bound) for word in words)
    )


def make_problem_alternative(
        words,
        x_bound,
        y_bound,
        options: CrosswordOptions = None
):
    if guaranteed_infeasible(words, x_bound, y_bound):
        return [], [], [], [], [], []
    if options is None:
        options = CrosswordOptions()

    id_pool = IDPool()
    clauses = []
    possible_placements = [[] for _ in words]
    for iw, w in enumerate(words):
        for is_horizontal in (True, False):
            for x in range(x_bound - ((len(w) - 1) if is_horizontal else 0)):
                for y in range(y_bound - ((len(w) - 1) if not is_horizontal else 0)):
                    possible_placements[iw].append((x, y, is_horizontal, id_pool.id()))
        clauses.extend(gen_uniqueness(list(v for _, _, _, v in possible_placements[iw])))
    pairwise_intersection_vars = [[[] for _ in words] for __ in words]
    for iw1, iw2 in combinations(range(len(words)), 2):
        pairwise_intersection_vars[iw2][iw1] = pairwise_intersection_vars[iw1][iw2]
    clauses.extend(generate_crossing_constraints_alternative(
        words, x_bound, y_bound, possible_placements,
        allowed_intersection_types=options.allowed_intersection_types,
        forbidden_crossings=options.forbidden_crossings,
        pairwise_intersection_vars=pairwise_intersection_vars,
        vpool=id_pool
    ))
    clauses.extend(bound_isolated_component_size(
        pairwise_intersection_vars,
        options.min_isolated_component_size,
        vpool=id_pool
    ))

    return list(set(map(tuple, map(sorted, clauses)))), words, possible_placements


def make_problem(
        words,
        x_bound,
        y_bound,
        options: CrosswordOptions = None
):
    if guaranteed_infeasible(words, x_bound, y_bound):
        return [], [], [], [], [], []
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
        clauses.extend(pysat_card.CardEnc.atleast(
            lits=is_placed[:n_original_words],
            bound=floor(n_original_words * (1 - options.max_skewness) * 0.5),
            encoding=pysat_card.EncType.seqcounter,
            vpool=id_pool).clauses
                       )
        clauses.extend(pysat_card.CardEnc.atmost(
            lits=is_placed[:n_original_words],
            bound=ceil(n_original_words * (1 + options.max_skewness) * 0.5),
            encoding=pysat_card.EncType.seqcounter,
            vpool=id_pool).clauses
                       )

    if options.allowed_intersection_types is None:
        options.allowed_intersection_types = [IntersectionType.CROSSING, IntersectionType.HORIZONTAL_OVERLAP,
         IntersectionType.VERTICAL_OVERLAP]

    clause_list, intersections_per_word = generate_crossing_constraints(
        words, is_in_hor_mode, is_x_coord, is_y_coord,
        allowed_intersection_types=options.allowed_intersection_types,
        forbidden_crossings=options.forbidden_crossings,
        register_intersections=True,
        vpool=id_pool
    )
    clauses.extend(clause_list)

    intersections_per_word = [set(intersections_per_word[iw]) | set(intersections_per_word[iw + n_original_words]) for iw
                              in range(n_original_words)]
    pairwise_intersection_vars = [[set() for _ in range(n_original_words)] for __ in range(n_original_words)]
    for iw1, iw2 in combinations(range(n_original_words), 2):
        pairwise_intersection_vars[iw1][iw2] = intersections_per_word[iw1] & intersections_per_word[iw2]
        pairwise_intersection_vars[iw2][iw1] = pairwise_intersection_vars[iw1][iw2]

    if options.required_crossings:
        for w1, w2 in options.required_crossings:
            clauses.append(list(pairwise_intersection_vars[words.index(w1)][words.index(w2)]))

    clauses.extend(bound_isolated_component_size(
        pairwise_intersection_vars,
        options.min_isolated_component_size,
        vpool=id_pool
    ))

    # if options.min_words_with_many_intersections is not None:
    #     new_vars = [id_pool.id() for _ in words]
    #     clauses.extend(
    #         clause + [-new_vars[iw]]
    #         for iw, lits in enumerate(intersection_vars)
    #         for clause in pysat_card.CardEnc.atleast(
    #             lits=lits,
    #             bound=options.min_words_with_many_intersections.intersections_bound,
    #             encoding=pysat_card.EncType.seqcounter,
    #             vpool=id_pool
    #         ).clauses
    #     )
    #     clauses.extend(
    #         pysat_card.CardEnc.atleast(
    #             lits=new_vars,
    #             bound=options.min_words_with_many_intersections.qty_bound,
    #             encoding=pysat_card.EncType.seqcounter,
    #             vpool=id_pool
    #         ).clauses
    #     )

    # clauses.extend(ensure_nonempty_first_row_and_column(is_x_coord, is_y_coord))
    clauses.extend(ensure_exactly_one_word_placement(words, is_in_hor_mode, is_x_coord, is_y_coord, is_placed))
    clauses.extend(forbid_cells(words, is_in_hor_mode, is_x_coord, is_y_coord, options.forbidden_cells))
    clauses.extend(require_placements(words, is_in_hor_mode, is_x_coord, is_y_coord, is_placed, options.required_placements))
    clauses.extend(forbid_placements(words, is_in_hor_mode, is_x_coord, is_y_coord, is_placed, options.forbidden_placements))

    print("Sorting and deduplicating...")
    return list(set(map(tuple, map(sorted, clauses)))), words, is_in_hor_mode, is_placed, is_x_coord, is_y_coord


def solve_problem(clauses, words, is_in_hor_mode, is_placed, is_x_coord, is_y_coord, SatSolver):
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


def solve_problem_alternative(clauses, words, possible_placements, SatSolver):
    with SatSolver() as solver:
        for clause in clauses:
            solver.add_clause(clause)

        if not solver.solve():
            return []

        model = solver.get_model()
        result = []
        for iw, w in enumerate(words):
            for x, y, is_horizontal, v in possible_placements[iw]:
                if v in model:
                    result.append(WordPlacement(word=w, x=x, y=y, horizontal=is_horizontal))
                    break
        return result


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


def save_solution(placement_data: list[WordPlacement], words_with_hints: list):
    placement_data = placement_data.copy()
    for data in placement_data:
        data.hint = next(w["hint"] for w in words_with_hints if w["word"] == data.word)
    jsonified = json.dumps(placement_data, cls=EnhancedJSONEncoder, indent=2)
    Path("output/output.js").write_text(f"var placement_data = {jsonified};")


def solve_from_json(params_json):
    kwargs = json.loads(params_json)
    words, x_bound, y_bound = kwargs["words"], kwargs["x_bound"], kwargs["y_bound"]
    for key in ("words", "x_bound", "y_bound"):
        kwargs.pop(key)
    crossword_options = None
    if kwargs:
        crossword_options = CrosswordOptions(**kwargs)

    stage_1_start = datetime.now()
    print("DIAG: Generating clauses...")
    clauses, words_extended, is_in_hor_mode, is_placed, is_x_coord, is_y_coord = make_problem(words, x_bound, y_bound, crossword_options)
    stage_2_start = datetime.now()
    print("DIAG: Clause generation took ", (stage_2_start - stage_1_start).total_seconds(), "s")
    print("DIAG: Number of clauses: ", len(clauses))

    print("DIAG: Solving...")
    placement_data = solve_problem(clauses, words_extended, is_in_hor_mode, is_placed, is_x_coord, is_y_coord, Mergesat3)
    stage_3_start = datetime.now()
    print("DIAG: Solving took ", (stage_3_start - stage_2_start).total_seconds(), "s")
    print("DIAG: Solution:")
    print_solution(placement_data, x_bound, y_bound)

    return json.dumps(placement_data, cls=EnhancedJSONEncoder)


def test():
    words_with_hints = [
       {"word": "spoon", "hint": "A small tool we use for stirring soup and eating cereal."},
       {"word": "fork", "hint": "It has three points; we use to pick up food like vegetables or meat."},
       {"word": "pan", "hint": "We cook pancakes on this round, flat plate with a handle."},
       {"word": "colander", "hint": "A bowl-shaped thing we use to drain water from pasta."},
       {"word": "blender", "hint": "It's like a big machine that mixes food into smoothies or soups."},
       {"word": "oven", "hint": "A place where we bake cookies and cakes to be yummy and hot."},
       {"word": "spatula", "hint": "This flat tool helps us flip pancakes without breaking them."},
       {"word": "whisk", "hint": "We use it to mix things like eggs or cream really well."},
       {"word": "tongs", "hint": "A pair of tools with arms that help us pick up hot food from the stove."},
       {"word": "mixer", "hint": "It has blades that spin around; we use it for making dough or whipping cream."},
       {"word": "grater", "hint": "This tool with sharp holes helps us shred cheese into small pieces."},
       {"word": "ladle", "hint": "It's a big spoon for scooping soup or stew into bowls."},
       {"word": "peeler", "hint": "A small tool that takes off the skin of fruits and vegetables like apples."},
       {"word": "scissors", "hint": "We use these to cut paper, but not for food; they're kitchen scissors."},
       {"word": "thermometer", "hint": "A tool that tells us how hot our cooked meat is before we eat it."},
    ]
    # words_with_hints = [    {"word": "elephant", "hint": "A large animal with a trunk and big ears, known for its memory."},    {"word": "giraffe", "hint": "This animal has a very long neck and eats leaves from tall trees."},    {"word": "tiger", "hint": "A big cat with orange fur and black stripes, known for its strength."},    {"word": "zebra", "hint": "A horse-like animal with distinctive black and white stripes."},    {"word": "kangaroo", "hint": "An Australian animal that hops and carries its baby in a pouch."},    {"word": "penguin", "hint": "A flightless bird that swims in cold water and has a tuxedo-like appearance."},    {"word": "lion", "hint": "Known as the king of the jungle, this big cat has a majestic mane."},    {"word": "monkey", "hint": "A playful animal that loves to swing from tree branches."},    {"word": "bear", "hint": "A large, strong animal that can be brown, black, or white; often found in forests."},    {"word": "rabbit", "hint": "A small, furry animal with long ears that loves to hop and eat carrots."},    {"word": "ant", "hint": "A tiny insect that lives in colonies and works hard to collect food."},    {"word": "rat", "hint": "A small rodent with a long tail, often found in urban areas."},    {"word": "bee", "hint": "An insect that makes honey and is known for its buzzing sound."},    {"word": "turtle", "hint": "A slow-moving reptile with a hard shell that lives on land or in water."},    {"word": "frog", "hint": "An amphibian that hops and has smooth, moist skin."},    {"word": "duck", "hint": "A bird that swims in ponds and makes a quacking sound."},    {"word": "fish", "hint": "An aquatic animal that breathes through gills and swims with fins."},    {"word": "shark", "hint": "A large, predatory fish known for its sharp teeth and dorsal fin."},    {"word": "whale", "hint": "A massive marine mammal that can sing underwater and spouts water."},    {"word": "dolphin", "hint": "A friendly and intelligent marine mammal known for its playful behavior."},    {"word": "octopus", "hint": "A sea creature with eight arms and a soft, flexible body."},    {"word": "butterfly", "hint": "An insect with colorful wings that flies from flower to flower."},    {"word": "swan", "hint": "A graceful bird with a long neck that glides on water."},    {"word": "eagle", "hint": "A powerful bird of prey with sharp talons and excellent vision."},    {"word": "owl", "hint": "A nocturnal bird with big eyes and a hooting call."},    {"word": "parrot", "hint": "A colorful bird known for its ability to mimic human speech."},    {"word": "bat", "hint": "A nocturnal mammal that can fly and uses echolocation to navigate."}]


    words = [w["word"].lower() for w in words_with_hints]

    words = [
        "elephant", "giraffe", "tiger", "zebra", "kangaroo", "penguin", "lion", "monkey", "bear", "rabbit", "ant", "rat", "bee",
        "turtle", "frog", "duck", "fish", "shark", "whale", "dolphin", "octopus", "butterfly", "swan", "eagle", "owl", "parrot", "bat"
    ]

    # possible for total connectivity,
    # x_bound, y_bound = 18, 11
    # smallest area, very good with Lingeling for component size = 4
    # x_bound, y_bound = 8, 11
    # x_bound, y_bound = 11, 11

    # var placement_data = [{"word": "cake", "x": 6, "y": 9, "horizontal": true}, {"word": "soda", "x": 4, "y": 4, "horizontal": true}, {"word": "salad", "x": 1, "y": 7, "horizontal": true}, {"word": "sushi", "x": 4, "y": 3, "horizontal": true}, {"word": "pasta", "x": 1, "y": 9, "horizontal": true}, {"word": "corn", "x": 3, "y": 6, "horizontal": true}, {"word": "bean", "x": 0, "y": 4, "horizontal": true}, {"word": "chef", "x": 5, "y": 0, "horizontal": true}, {"word": "menu", "x": 5, "y": 2, "horizontal": true}, {"word": "plate", "x": 3, "y": 1, "horizontal": true}, {"word": "feast", "x": 0, "y": 5, "horizontal": true}, {"word": "taste", "x": 2, "y": 8, "horizontal": true}, {"word": "table", "x": 5, "y": 5, "horizontal": true}, {"word": "pizza", "x": 2, "y": 0, "horizontal": false}, {"word": "juice", "x": 1, "y": 0, "horizontal": false}, {"word": "burger", "x": 9, "y": 1, "horizontal": false}, {"word": "toast", "x": 4, "y": 5, "horizontal": false}, {"word": "fruit", "x": 8, "y": 0, "horizontal": false}, {"word": "milk", "x": 8, "y": 6, "horizontal": false}, {"word": "rice", "x": 9, "y": 6, "horizontal": false}, {"word": "fork", "x": 0, "y": 5, "horizontal": false}, {"word": "spoon", "x": 3, "y": 0, "horizontal": false}, {"word": "bowl", "x": 7, "y": 5, "horizontal": false}, {"word": "glass", "x": 4, "y": 0, "horizontal": false}];
    # var placement_data = [{"word": "elephant", "x": 1, "y": 11, "horizontal": true}, {"word": "giraffe", "x": 1, "y": 1, "horizontal": true}, {"word": "tiger", "x": 1, "y": 8, "horizontal": true}, {"word": "bear", "x": 1, "y": 9, "horizontal": true}, {"word": "rabbit", "x": 4, "y": 9, "horizontal": true}, {"word": "ant", "x": 6, "y": 11, "horizontal": true}, {"word": "frog", "x": 7, "y": 3, "horizontal": true}, {"word": "duck", "x": 8, "y": 8, "horizontal": true}, {"word": "whale", "x": 1, "y": 4, "horizontal": true}, {"word": "dolphin", "x": 0, "y": 0, "horizontal": true}, {"word": "butterfly", "x": 2, "y": 10, "horizontal": true}, {"word": "eagle", "x": 1, "y": 7, "horizontal": true}, {"word": "parrot", "x": 0, "y": 5, "horizontal": true}, {"word": "bat", "x": 4, "y": 3, "horizontal": true}, {"word": "zebra", "x": 8, "y": 0, "horizontal": false}, {"word": "kangaroo", "x": 10, "y": 0, "horizontal": false}, {"word": "penguin", "x": 0, "y": 5, "horizontal": false}, {"word": "lion", "x": 2, "y": 0, "horizontal": false}, {"word": "monkey", "x": 11, "y": 5, "horizontal": false}, {"word": "rat", "x": 5, "y": 8, "horizontal": false}, {"word": "bee", "x": 1, "y": 9, "horizontal": false}, {"word": "turtle", "x": 6, "y": 3, "horizontal": false}, {"word": "fish", "x": 7, "y": 3, "horizontal": false}, {"word": "shark", "x": 3, "y": 2, "horizontal": false}, {"word": "octopus", "x": 9, "y": 0, "horizontal": false}, {"word": "swan", "x": 1, "y": 3, "horizontal": false}, {"word": "owl", "x": 4, "y": 5, "horizontal": false}];
    # var placement_data3 = [{"word": "street", "x": 5, "y": 10, "horizontal": true}, {"word": "bus", "x": 3, "y": 10, "horizontal": true}, {"word": "tree", "x": 6, "y": 10, "horizontal": true}, {"word": "garden", "x": 0, "y": 4, "horizontal": true}, {"word": "kitchen", "x": 0, "y": 1, "horizontal": true}, {"word": "bedroom", "x": 3, "y": 6, "horizontal": true}, {"word": "bathroom", "x": 1, "y": 2, "horizontal": true}, {"word": "playground", "x": 0, "y": 0, "horizontal": true}, {"word": "restaurant", "x": 0, "y": 9, "horizontal": true}, {"word": "bridge", "x": 0, "y": 5, "horizontal": true}, {"word": "museum", "x": 1, "y": 8, "horizontal": true}, {"word": "traffic", "x": 0, "y": 3, "horizontal": true}, {"word": "house", "x": 2, "y": 6, "horizontal": false}, {"word": "apartment", "x": 9, "y": 1, "horizontal": false}, {"word": "park", "x": 0, "y": 7, "horizontal": false}, {"word": "school", "x": 7, "y": 3, "horizontal": false}, {"word": "store", "x": 8, "y": 4, "horizontal": false}, {"word": "car", "x": 6, "y": 3, "horizontal": false}, {"word": "library", "x": 1, "y": 0, "horizontal": false}, {"word": "supermarket", "x": 10, "y": 0, "horizontal": false}];

    stats = []

    for size in range(14, 13, -1):
        for modeling_type in ("alternative", ):
            x_bound = size
            y_bound = size
            stage_1_start = datetime.now()
            print("Generating clauses...")
            if modeling_type == "main":
                clauses, words_extended, is_in_hor_mode, is_placed, is_x_coord, is_y_coord = make_problem(
                    words, x_bound, y_bound,
                    CrosswordOptions(
                        min_isolated_component_size=19,
                        allowed_intersection_types=[IntersectionType.CROSSING, IntersectionType.HORIZONTAL_OVERLAP, IntersectionType.VERTICAL_OVERLAP]
                    )
                )
            else:
                clauses, words, possible_placements = make_problem_alternative(
                    words,
                    x_bound,
                    y_bound,
                    CrosswordOptions(
                           min_isolated_component_size=19,
                           allowed_intersection_types=[IntersectionType.CROSSING, IntersectionType.HORIZONTAL_OVERLAP, IntersectionType.VERTICAL_OVERLAP]
                       )
                )
            stage_2_start = datetime.now()
            print("Clause generation took ", (stage_2_start - stage_1_start).total_seconds(), "s")
            print("Number of clauses: ", len(clauses))
            for solver in ( Mergesat3, ): # Glucose4, MinisatGH, MergeSat3
                print("Solving with", solver.__name__)
                stage_2_start = datetime.now()
                if modeling_type == "main":
                    placement_data = solve_problem(clauses, words_extended, is_in_hor_mode, is_placed, is_x_coord, is_y_coord, solver)
                else:
                    placement_data = solve_problem_alternative(clauses, words, possible_placements, solver)
                stage_3_start = datetime.now()
                elapsed_time = (stage_3_start - stage_2_start).total_seconds()
                stats.append((modeling_type, len(words), size, solver.__name__, elapsed_time))
                print("Solving took ", elapsed_time, "s")

            print("Solution:")
            print_solution(placement_data, x_bound, y_bound)

    print(json.dumps(stats, indent=2))

    # save_solution(placement_data, words_with_hints)


if __name__ == '__main__':
    test()
