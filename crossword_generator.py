import warnings

warnings.filterwarnings("ignore")

import argparse
import dataclasses
import json
from datetime import datetime
from enum import IntEnum
from itertools import combinations, product
from pathlib import Path
from typing import Any, Iterable, Optional

import pysat.card as pysat_card
from pysat.formula import IDPool
from pysat.solvers import Glucose4, Mergesat3, Lingeling, MinisatGH, CryptoMinisat


class IntersectionType(IntEnum):
    CROSSING = 0
    HORIZONTAL_OVERLAP = 1
    VERTICAL_OVERLAP = 2


@dataclasses.dataclass
class WordPlacement:
    word: int
    horizontal: bool
    x: Optional[int]
    y: Optional[int]


@dataclasses.dataclass
class IntersectionOptions:
    intersections_bound: int
    qty_bound: int


@dataclasses.dataclass
class CrosswordOptions:
    min_isolated_component_size: int = 2
    allowed_intersection_types: list[IntersectionType] = None
    min_words_with_many_intersections: IntersectionOptions = None
    forbidden_cells: list[tuple[int, int]] = None
    required_placements: list[WordPlacement] = None
    forbidden_placements: list[WordPlacement] = None
    required_crossings: list[tuple[int, int]] = None
    forbidden_crossings: list[tuple[int, int]] = None

    def __post_init__(self):
        if self.forbidden_placements:
            self.forbidden_placements = [
                WordPlacement(**data) if isinstance(data, dict) else data for data in self.forbidden_placements
            ]
        if self.required_placements:
            self.required_placements = [
                WordPlacement(**data) if isinstance(data, dict) else data for data in self.required_placements
            ]
        if isinstance(self.min_words_with_many_intersections, dict):
            self.min_words_with_many_intersections = IntersectionOptions(**self.min_words_with_many_intersections)


class EnhancedJSONEncoder(json.JSONEncoder):
    def default(self, obj):
        if dataclasses.is_dataclass(obj):
            return dataclasses.asdict(obj)
        return super().default(obj)


def compatibility_check(w1, is_hor_1, w2, is_hor_2, dx, dy):
    if is_hor_1 == is_hor_2:
        dc, dco = (dx, dy) if is_hor_1 else (dy, dx)
        if dco != 0 or dc <= -len(w1) or dc >= len(w2):
            return True, None
        if dc >= 0:
            dc, w1, w2 = -dc, w2, w1
        return w1[-dc : len(w2) - dc] == w2[: min(len(w2), len(w1) + dc)], (
            IntersectionType.HORIZONTAL_OVERLAP if is_hor_1 else IntersectionType.VERTICAL_OVERLAP
        )

    if not is_hor_1:
        dx, dy = dy, dx
    if dy < 0 or dy >= len(w2) or dx > 0 or dx <= -len(w1):
        return True, None
    return w1[-dx] == w2[dy], IntersectionType.CROSSING


def generate_crossing_constraints_alternative(
    words,
    x_bound,
    y_bound,
    v_cache,
    allowed_intersection_types: Iterable[IntersectionType] = None,
    forbidden_crossings: Iterable[tuple[int, int]] = None,
    pairwise_intersection_vars=None,
    vpool: IDPool = None,
):
    if pairwise_intersection_vars is not None and vpool is None:
        raise ValueError("vpool must be provided if register_intersections is True")
    if allowed_intersection_types is None:
        allowed_intersection_types = (
            IntersectionType.HORIZONTAL_OVERLAP,
            IntersectionType.VERTICAL_OVERLAP,
            IntersectionType.CROSSING,
        )

    allowed_intersection_types = set(allowed_intersection_types) | {None}
    forbidden_crossings = set(forbidden_crossings) if forbidden_crossings else set()

    for (iw1, w1), (iw2, w2) in combinations(enumerate(words), 2):
        is_crossing_forbidden = (iw1, iw2) in forbidden_crossings
        for is_hor_1, is_hor_2 in product((False, True), repeat=2):
            cache_1 = v_cache[iw1][is_hor_1]
            cache_2 = v_cache[iw2][is_hor_2]
            compatibility_cache = tuple(
                tuple(compatibility_check(w1, is_hor_1, w2, is_hor_2, dx, dy) for dy in range(-y_bound, y_bound))
                for dx in range(-x_bound, x_bound)
            )

            if is_hor_1 == is_hor_2:
                if is_hor_1:
                    for y in range(y_bound):
                        for x1, x2 in product(range(x_bound - len(w1) + 1), range(x_bound - len(w2) + 1)):
                            are_compatible, intersection_type = compatibility_cache[x1 - x2 + x_bound][y_bound]
                            if (
                                not are_compatible
                                or intersection_type not in allowed_intersection_types
                                or intersection_type is not None
                                and is_crossing_forbidden
                            ):
                                yield [-cache_1[x1][y], -cache_2[x2][y]]
                            elif (
                                are_compatible
                                and intersection_type is not None
                                and not is_crossing_forbidden
                                and pairwise_intersection_vars is not None
                            ):
                                new_var = vpool.id()
                                yield from gen_conjunction(new_var, [cache_1[x1][y], cache_2[x2][y]])
                                pairwise_intersection_vars[iw1][iw2].append(new_var)
                else:
                    for x in range(x_bound):
                        for y1, y2 in product(range(y_bound - len(w1) + 1), range(y_bound - len(w2) + 1)):
                            are_compatible, intersection_type = compatibility_cache[x_bound][y1 - y2 + y_bound]
                            if (
                                not are_compatible
                                or intersection_type not in allowed_intersection_types
                                or intersection_type is not None
                                and is_crossing_forbidden
                            ):
                                yield [-cache_1[x][y1], -cache_2[x][y2]]
                            elif (
                                are_compatible
                                and intersection_type is not None
                                and not is_crossing_forbidden
                                and pairwise_intersection_vars is not None
                            ):
                                new_var = vpool.id()
                                yield from gen_conjunction(new_var, [cache_1[x][y1], cache_2[x][y2]])
                                pairwise_intersection_vars[iw1][iw2].append(new_var)
            else:
                if is_hor_1:
                    for x1, y1 in product(range(x_bound - len(w1) + 1), range(y_bound)):
                        for x2, y2 in product(
                            range(x1, x1 + len(w1)), range(max(0, y1 - len(w2) + 1), min(y1 + 1, y_bound - len(w2) + 1))
                        ):
                            are_compatible, intersection_type = compatibility_cache[x1 - x2 + x_bound][
                                y1 - y2 + y_bound
                            ]
                            if (
                                not are_compatible
                                or intersection_type not in allowed_intersection_types
                                or intersection_type is not None
                                and is_crossing_forbidden
                            ):
                                yield [-cache_1[x1][y1], -cache_2[x2][y2]]
                            elif (
                                are_compatible
                                and intersection_type is not None
                                and not is_crossing_forbidden
                                and pairwise_intersection_vars is not None
                            ):
                                new_var = vpool.id()
                                yield from gen_conjunction(new_var, [cache_1[x1][y1], cache_2[x2][y2]])
                                pairwise_intersection_vars[iw1][iw2].append(new_var)
                else:
                    for x1, y1 in product(range(x_bound), range(y_bound - len(w1) + 1)):
                        for x2, y2 in product(
                            range(max(0, x1 - len(w2) + 1), min(x1 + 1, x_bound - len(w2) + 1)), range(y1, y1 + len(w1))
                        ):
                            are_compatible, intersection_type = compatibility_cache[x1 - x2 + x_bound][
                                y1 - y2 + y_bound
                            ]
                            if (
                                not are_compatible
                                or intersection_type not in allowed_intersection_types
                                or intersection_type is not None
                                and is_crossing_forbidden
                            ):
                                yield [-cache_1[x1][y1], -cache_2[x2][y2]]
                            elif (
                                are_compatible
                                and intersection_type is not None
                                and not is_crossing_forbidden
                                and pairwise_intersection_vars is not None
                            ):
                                new_var = vpool.id()
                                yield from gen_conjunction(new_var, [cache_1[x1][y1], cache_2[x2][y2]])
                                pairwise_intersection_vars[iw1][iw2].append(new_var)


def ensure_nonempty_first_row_and_column(is_x_coord, is_y_coord):
    return [[var_list[0] for var_list in is_x_coord if var_list], [var_list[0] for var_list in is_y_coord if var_list]]


def forbid_cells(words, placement_vars, forbidden_cells: list[tuple[int, int]]):
    if not forbidden_cells:
        return
    for iw, w in enumerate(words):
        forbidden_vars = set()
        for x_forbidden, y_forbidden in forbidden_cells:
            for x in range(max(0, x_forbidden - len(w) + 1), min(x_forbidden + 1, len(placement_vars[iw][1]))):
                forbidden_vars.add(placement_vars[iw][True][x][y_forbidden])
            for y in range(max(0, y_forbidden - len(w) + 1), min(y_forbidden + 1, len(placement_vars[iw][0][0]))):
                forbidden_vars.add(placement_vars[iw][False][x_forbidden][y])
        yield from ([-v] for v in forbidden_vars)


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
    reachability_vars = cumulative_pairwise_intersection_vars
    max_distance = n_unique_words - 1
    for _ in range(n_unique_words):
        max_distance = (max_distance + 1) // 2

        reachability_2_vars: Any = [[None] * n_unique_words for _ in range(n_unique_words)]
        for iw1, iw2 in combinations(range(n_unique_words), 2):
            common_neighbours = [reachability_vars[iw1][iw2]] if reachability_vars[iw1][iw2] is not None else []
            for iw in set(range(n_unique_words)) - {iw1, iw2}:
                if reachability_vars[iw1][iw] is not None and reachability_vars[iw2][iw] is not None:
                    common_neighbours.append(vpool.id())
                    yield from gen_conjunction(
                        common_neighbours[-1], [reachability_vars[iw1][iw], reachability_vars[iw2][iw]]
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


def require_placements(placement_vars, required_placements: Iterable[WordPlacement]):
    if not required_placements:
        return
    for word_placement in required_placements:
        clause = []
        for x, y_vars in enumerate(placement_vars[word_placement.word][word_placement.horizontal]):
            for y, v in enumerate(y_vars):
                if (word_placement.x is None or word_placement.x == x) and (
                    word_placement.y is None or word_placement.y == y
                ):
                    clause.append(v)
        yield clause


def forbid_placements(placement_vars, forbidden_placements: Iterable[WordPlacement]):
    if not forbidden_placements:
        return
    for word_placement in forbidden_placements:
        for is_hor in (0, 1):
            if word_placement.horizontal is None or int(word_placement.horizontal) == is_hor:
                for x, y_vars in enumerate(placement_vars[word_placement.word][is_hor]):
                    if word_placement.x is None or word_placement.x == x:
                        for y, v in enumerate(y_vars):
                            if word_placement.y is None or word_placement.y == y:
                                yield [-v]


def guaranteed_infeasible(words, x_bound, y_bound):
    return (
        x_bound < 1
        or y_bound < 1
        or sum(map(len, words)) > 2 * x_bound * y_bound
        or any(len(word) > max(x_bound, y_bound) for word in words)
    )


def bound_number_of_intersections(
    n_words, pairwise_intersection_vars, id_pool, min_words_with_many_intersections: IntersectionOptions
):
    if min_words_with_many_intersections is None:
        return
    single_intersection_vars = [[] for _ in range(n_words)]
    for iw1, iw2 in combinations(range(n_words), 2):
        if not pairwise_intersection_vars[iw1][iw2]:
            continue
        intersection_iw1_iw2 = id_pool.id()
        single_intersection_vars[iw1].append(intersection_iw1_iw2)
        single_intersection_vars[iw2].append(intersection_iw1_iw2)
        yield from gen_disjunction(intersection_iw1_iw2, pairwise_intersection_vars[iw1][iw2], True)

    new_vars = [id_pool.id() for _ in range(n_words)]
    yield from pysat_card.CardEnc.atleast(
        lits=new_vars,
        bound=min_words_with_many_intersections.qty_bound,
        encoding=pysat_card.EncType.seqcounter,
        vpool=id_pool,
    ).clauses
    for iw in range(n_words):
        if len(single_intersection_vars[iw]) >= min_words_with_many_intersections.intersections_bound:
            yield from (
                clause + [-new_vars[iw]]
                for clause in pysat_card.CardEnc.atleast(
                    lits=single_intersection_vars[iw],
                    bound=min_words_with_many_intersections.intersections_bound,
                    encoding=pysat_card.EncType.seqcounter,
                    vpool=id_pool,
                ).clauses
            )
        else:
            yield [-new_vars[iw]]


def make_problem(words, x_bound, y_bound, options: CrosswordOptions = None):
    if guaranteed_infeasible(words, x_bound, y_bound):
        return [], []
    if options is None:
        options = CrosswordOptions()

    id_pool = IDPool()
    clauses = []

    placement_vars = tuple(
        tuple(
            tuple(
                tuple(id_pool.id() for __ in range(y_bound - ((len(w) - 1) if not is_hor else 0)))
                for _ in range(x_bound - ((len(w) - 1) if is_hor else 0))
            )
            for is_hor in (0, 1)
        )
        for w in words
    )

    for word_placements in placement_vars:
        clauses.extend(gen_uniqueness([v for hvars in word_placements for yvars in hvars for v in yvars]))

    pairwise_intersection_vars = [[[] for _ in words] for __ in words]
    for iw1, iw2 in combinations(range(len(words)), 2):
        pairwise_intersection_vars[iw2][iw1] = pairwise_intersection_vars[iw1][iw2]

    clauses.extend(
        generate_crossing_constraints_alternative(
            words,
            x_bound,
            y_bound,
            placement_vars,
            allowed_intersection_types=options.allowed_intersection_types,
            forbidden_crossings=options.forbidden_crossings,
            pairwise_intersection_vars=pairwise_intersection_vars,
            vpool=id_pool,
        )
    )

    if options.required_crossings:
        if not all(pairwise_intersection_vars[iw1][iw2] for iw1, iw2 in options.required_crossings):
            print(
                "Warning: provided required crossings are not all feasible. Taking only feasible crossings into account."
            )
        clauses.extend(
            pairwise_intersection_vars[iw1][iw2]
            for iw1, iw2 in options.required_crossings
            if pairwise_intersection_vars[iw1][iw2]
        )

    clauses.extend(
        bound_isolated_component_size(pairwise_intersection_vars, options.min_isolated_component_size, vpool=id_pool)
    )

    if options.min_words_with_many_intersections is not None:
        clauses.extend(
            bound_number_of_intersections(
                len(words), pairwise_intersection_vars, id_pool, options.min_words_with_many_intersections
            )
        )

    # ensure non-empty first row and column; slows things down for sparse grids
    clauses.append(
        [
            vars_[is_horizontal][0][y]
            for vars_ in placement_vars
            for is_horizontal in (0, 1)
            for y in range(len(vars_[is_horizontal][0]) if vars_[is_horizontal] else 0)
        ]
    )
    clauses.append(
        [
            vars_[is_horizontal][x][0]
            for vars_ in placement_vars
            for is_horizontal in (0, 1)
            for x in range(len(vars_[is_horizontal]))
            if vars_[is_horizontal][x]
        ]
    )

    clauses.extend(forbid_cells(words, placement_vars, options.forbidden_cells))
    clauses.extend(require_placements(placement_vars, options.required_placements))
    clauses.extend(forbid_placements(placement_vars, options.forbidden_placements))

    return placement_vars, list(set(map(tuple, map(sorted, clauses))))


def solve_problem(words, placement_vars, clauses, solver_class):
    with solver_class() as solver:
        for clause in clauses:
            solver.add_clause(clause)

        if not solver.solve():
            return []

        model = solver.get_model()
        result = []
        for iw in range(len(words)):
            for is_horizontal, is_hor_vars in enumerate(placement_vars[iw]):
                for x, y_vars in enumerate(is_hor_vars):
                    for y, v in enumerate(y_vars):
                        if v in model:
                            result.append(WordPlacement(word=iw, x=x, y=y, horizontal=bool(is_horizontal)))
                            break
        return result


def get_bounds_from_solution(words, placement_data: list[WordPlacement]):
    x_bound = 0
    y_bound = 0

    for data in placement_data:
        for i, c in enumerate(words[data.word]):
            if data.horizontal:
                x_bound = max(x_bound, data.x + i + 1)
            else:
                y_bound = max(y_bound, data.y + i + 1)

    return x_bound, y_bound


def print_solution(words, placement_data: list[WordPlacement], x_bound, y_bound):
    grid = [["·"] * x_bound for _ in range(y_bound)]

    for data in placement_data:
        for i, c in enumerate(words[data.word]):
            if data.horizontal:
                if grid[data.y][data.x + i] not in ("·", c):
                    print("Conflict at", data.x + i, data.y)
                grid[data.y][data.x + i] = c
            else:
                if grid[data.y + i][data.x] not in ("·", c):
                    print("Conflict at", data.x, data.y + i)
                grid[data.y + i][data.x] = c

    print("\n".join(" ".join(row) for row in grid))


def save_solution(path: Path, placement_data: list[WordPlacement], words_with_hints: list):
    path.write_text(
        json.dumps(
            [
                {
                    "word": words_with_hints[data.word]["word"]
                    if isinstance(words_with_hints[data.word], dict)
                    else words_with_hints[data.word],
                    "x": data.x,
                    "y": data.y,
                    "horizontal": data.horizontal,
                    "hint": words_with_hints[data.word]["hint"]
                    if isinstance(words_with_hints[data.word], dict)
                    else words_with_hints[data.word],
                }
                for data in placement_data
            ],
            indent=2,
        )
    )


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
    placement_vars, clauses = make_problem(words, x_bound, y_bound, crossword_options)
    stage_2_start = datetime.now()
    print("DIAG: Clause generation took ", (stage_2_start - stage_1_start).total_seconds(), "s")
    print("DIAG: Number of clauses: ", len(clauses))

    print("DIAG: Solving...")
    placement_data = solve_problem(words, placement_vars, clauses, Mergesat3)
    stage_3_start = datetime.now()
    print("DIAG: Solving took ", (stage_3_start - stage_2_start).total_seconds(), "s")
    print("DIAG: Solution:")
    print_solution(words, placement_data, x_bound, y_bound)

    return json.dumps(placement_data, cls=EnhancedJSONEncoder)


def parse_args():
    parser = argparse.ArgumentParser(description="Crossword Creator CLI")
    parser.add_argument("--x_bound", type=int, required=True, help="Width of the crossword grid")
    parser.add_argument("--y_bound", type=int, required=True, help="Height of the crossword grid")
    parser.add_argument(
        "--words", type=str, help="Comma-separated list of words or path to a JSON file containing words and hints"
    )
    parser.add_argument("--input", type=Path, required=False, help="Input file path")
    parser.add_argument("--output", type=Path, required=False, help="Output file path")
    parser.add_argument(
        "--solver",
        type=str,
        default="Mergesat",
        required=False,
        help="Solver name (Glucose, Mergesat, Lingeling, MinisatGH, CryptoMinisat)",
    )
    parser.add_argument("--options", type=Path, required=False, help="Path to a JSON file containing crossword options")
    parser.add_argument(
        "--connected", type=bool, required=False, default=True, help="Require the crossword to be connected"
    )

    return parser.parse_args()


def main():
    args = parse_args()
    solver_class = Mergesat3
    if args.solver:
        match args.solver.lower():
            case "glucose":
                solver_class = Glucose4
            case "mergesat":
                solver_class = Mergesat3
            case "lingeling":
                solver_class = Lingeling
            case "minisatgh":
                solver_class = MinisatGH
            case "cryptominisat":
                solver_class = CryptoMinisat
            case _:
                print(f'Invalid solver name: "{args.solver}". Using Mergesat3.')

    if input_file := args.input:
        words_with_hints = json.loads(input_file.read_text())
        words = [(w["word"].lower() if isinstance(w, dict) else w.lower()) for w in words_with_hints]
        print(f"Loaded {len(words)} words from file {input_file.name}")
    elif args.words:
        words = [w.strip().lower() for w in args.words.split(",")]
        words_with_hints = words
        print(f"Loaded {len(words)} words from command line")
    else:
        print("No words provided")
        return

    if args.options:
        with open(args.options, "r") as f:
            options = CrosswordOptions(**json.load(f))
    elif args.connected:
        options = CrosswordOptions(
            min_isolated_component_size=len(words),
        )
    else:
        options = None

    if guaranteed_infeasible(words, args.x_bound, args.y_bound):
        print("No solution possible for provided words and grid size")
        return

    print("Generating SAT constraints")
    placement_vars, clauses = make_problem(words, args.x_bound, args.y_bound, options)
    print(f"Got {len(clauses)} constraints; solving SAT problem using {solver_class.__name__}…")
    solving_start_time = datetime.now()
    placement_data = solve_problem(words, placement_vars, clauses, solver_class)
    solving_end_time = datetime.now()
    print(f"Solving finished in {(solving_end_time - solving_start_time).total_seconds()} seconds.", end="")
    x_bound, y_bound = get_bounds_from_solution(words, placement_data)
    if x_bound:
        print(" Generated crossword:")
    else:
        print(" No solution found")
        return

    print_solution(words, placement_data, x_bound, y_bound)

    if output_file := args.output:
        save_solution(output_file, placement_data, words_with_hints)
        print(f"Solution saved to {output_file}")


if __name__ == "__main__":
    main()
