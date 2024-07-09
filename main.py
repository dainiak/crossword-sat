import dataclasses
import json
from datetime import datetime
from enum import IntEnum
from itertools import combinations, product
from pathlib import Path
from typing import Any, Iterable
from tqdm import tqdm

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

    for (iw1, w1), (iw2, w2) in tqdm(combinations(enumerate(words), 2), total=len(words) * (len(words) - 1) // 2):
        is_crossing_forbidden = (w1, w2) in forbidden_crossings
        for is_hor_1, is_hor_2 in product((False, True), repeat=2):
            cache_1 = v_cache[iw1][is_hor_1]
            cache_2 = v_cache[iw2][is_hor_2]
            compatibility_cache = tuple(
                tuple(
                    compatibility_check(w1, is_hor_1, w2, is_hor_2, dx, dy)
                    for dy in range(-y_bound, y_bound)
                )
                for dx in range(-x_bound, x_bound)
            )

            if is_hor_1 == is_hor_2:
                if is_hor_1:
                    for y in range(y_bound):
                        for x1, x2 in product(range(x_bound - len(w1) + 1), range(x_bound - len(w2) + 1)):
                            are_compatible, intersection_type = compatibility_cache[x1 - x2 + x_bound][y_bound]
                            if not are_compatible or intersection_type not in allowed_intersection_types or intersection_type is not None and is_crossing_forbidden:
                                yield [-cache_1[x1][y], -cache_2[x2][y]]
                            elif are_compatible and intersection_type is not None and not is_crossing_forbidden and pairwise_intersection_vars is not None:
                                new_var = vpool.id()
                                yield from gen_conjunction(new_var, [cache_1[x1][y], cache_2[x2][y]])
                                pairwise_intersection_vars[iw1][iw2].append(new_var)
                else:
                    for x in range(x_bound):
                        for y1, y2 in product(range(y_bound - len(w1) + 1), range(y_bound - len(w2) + 1)):
                            are_compatible, intersection_type = compatibility_cache[x_bound][y1 - y2 + y_bound]
                            if not are_compatible or intersection_type not in allowed_intersection_types or intersection_type is not None and is_crossing_forbidden:
                                yield [-cache_1[x][y1], -cache_2[x][y2]]
                            elif are_compatible and intersection_type is not None and not is_crossing_forbidden and pairwise_intersection_vars is not None:
                                new_var = vpool.id()
                                yield from gen_conjunction(new_var, [cache_1[x][y1], cache_2[x][y2]])
                                pairwise_intersection_vars[iw1][iw2].append(new_var)
            else:
                if is_hor_1:
                    for x1, y1 in product(range(x_bound - len(w1) + 1), range(y_bound)):
                        for x2, y2 in product(range(x1, x1 + len(w1)), range(max(0, y1 - len(w2) + 1), min(y1 + 1, y_bound - len(w2) + 1))):
                            are_compatible, intersection_type = compatibility_cache[x1 - x2 + x_bound][y1 - y2 + y_bound]
                            if not are_compatible or intersection_type not in allowed_intersection_types or intersection_type is not None and is_crossing_forbidden:
                                yield [-cache_1[x1][y1], -cache_2[x2][y2]]
                            elif are_compatible and intersection_type is not None and not is_crossing_forbidden and pairwise_intersection_vars is not None:
                                new_var = vpool.id()
                                yield from gen_conjunction(new_var, [cache_1[x1][y1], cache_2[x2][y2]])
                                pairwise_intersection_vars[iw1][iw2].append(new_var)
                else:
                    for x1, y1 in product(range(x_bound), range(y_bound - len(w1) + 1)):
                        for x2, y2 in product(range(max(0, x1 - len(w2) + 1), min(x1 + 1, x_bound - len(w2) + 1)), range(y1, y1 + len(w1))):
                            are_compatible, intersection_type = compatibility_cache[x1 - x2 + x_bound][y1 - y2 + y_bound]
                            if not are_compatible or intersection_type not in allowed_intersection_types or intersection_type is not None and is_crossing_forbidden:
                                yield [-cache_1[x1][y1], -cache_2[x2][y2]]
                            elif are_compatible and intersection_type is not None and not is_crossing_forbidden and pairwise_intersection_vars is not None:
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
    # clauses.extend(ensure_exactly_one_word_placement(words, is_in_hor_mode, is_x_coord, is_y_coord, is_placed))
    # clauses.extend(forbid_cells(words, is_in_hor_mode, is_x_coord, is_y_coord, options.forbidden_cells))
    # clauses.extend(require_placements(words, is_in_hor_mode, is_x_coord, is_y_coord, is_placed, options.required_placements))
    # clauses.extend(forbid_placements(words, is_in_hor_mode, is_x_coord, is_y_coord, is_placed, options.forbidden_placements))

    print("Sorting and deduplicating...")


    return list(set(map(tuple, map(sorted, clauses)))), words, possible_placements


def solve_problem(clauses, words, possible_placements, SatSolver):
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

    # words = [
    #     "elephant", "giraffe", "tiger", "zebra", "kangaroo", "penguin", "lion", "monkey", "bear", "rabbit", "ant", "rat", "bee",
    #     "turtle", "frog", "duck", "fish", "shark", "whale", "dolphin", "octopus", "butterfly", "swan", "eagle", "owl", "parrot", "bat"
    # ]

    # possible for total connectivity,
    # x_bound, y_bound = 18, 11
    # smallest area, very good with Lingeling for component size = 4
    # x_bound, y_bound = 8, 11
    # x_bound, y_bound = 11, 11

    # var placement_data = [{"word": "cake", "x": 6, "y": 9, "horizontal": true}, {"word": "soda", "x": 4, "y": 4, "horizontal": true}, {"word": "salad", "x": 1, "y": 7, "horizontal": true}, {"word": "sushi", "x": 4, "y": 3, "horizontal": true}, {"word": "pasta", "x": 1, "y": 9, "horizontal": true}, {"word": "corn", "x": 3, "y": 6, "horizontal": true}, {"word": "bean", "x": 0, "y": 4, "horizontal": true}, {"word": "chef", "x": 5, "y": 0, "horizontal": true}, {"word": "menu", "x": 5, "y": 2, "horizontal": true}, {"word": "plate", "x": 3, "y": 1, "horizontal": true}, {"word": "feast", "x": 0, "y": 5, "horizontal": true}, {"word": "taste", "x": 2, "y": 8, "horizontal": true}, {"word": "table", "x": 5, "y": 5, "horizontal": true}, {"word": "pizza", "x": 2, "y": 0, "horizontal": false}, {"word": "juice", "x": 1, "y": 0, "horizontal": false}, {"word": "burger", "x": 9, "y": 1, "horizontal": false}, {"word": "toast", "x": 4, "y": 5, "horizontal": false}, {"word": "fruit", "x": 8, "y": 0, "horizontal": false}, {"word": "milk", "x": 8, "y": 6, "horizontal": false}, {"word": "rice", "x": 9, "y": 6, "horizontal": false}, {"word": "fork", "x": 0, "y": 5, "horizontal": false}, {"word": "spoon", "x": 3, "y": 0, "horizontal": false}, {"word": "bowl", "x": 7, "y": 5, "horizontal": false}, {"word": "glass", "x": 4, "y": 0, "horizontal": false}];
    # var placement_data = [{"word": "elephant", "x": 1, "y": 11, "horizontal": true}, {"word": "giraffe", "x": 1, "y": 1, "horizontal": true}, {"word": "tiger", "x": 1, "y": 8, "horizontal": true}, {"word": "bear", "x": 1, "y": 9, "horizontal": true}, {"word": "rabbit", "x": 4, "y": 9, "horizontal": true}, {"word": "ant", "x": 6, "y": 11, "horizontal": true}, {"word": "frog", "x": 7, "y": 3, "horizontal": true}, {"word": "duck", "x": 8, "y": 8, "horizontal": true}, {"word": "whale", "x": 1, "y": 4, "horizontal": true}, {"word": "dolphin", "x": 0, "y": 0, "horizontal": true}, {"word": "butterfly", "x": 2, "y": 10, "horizontal": true}, {"word": "eagle", "x": 1, "y": 7, "horizontal": true}, {"word": "parrot", "x": 0, "y": 5, "horizontal": true}, {"word": "bat", "x": 4, "y": 3, "horizontal": true}, {"word": "zebra", "x": 8, "y": 0, "horizontal": false}, {"word": "kangaroo", "x": 10, "y": 0, "horizontal": false}, {"word": "penguin", "x": 0, "y": 5, "horizontal": false}, {"word": "lion", "x": 2, "y": 0, "horizontal": false}, {"word": "monkey", "x": 11, "y": 5, "horizontal": false}, {"word": "rat", "x": 5, "y": 8, "horizontal": false}, {"word": "bee", "x": 1, "y": 9, "horizontal": false}, {"word": "turtle", "x": 6, "y": 3, "horizontal": false}, {"word": "fish", "x": 7, "y": 3, "horizontal": false}, {"word": "shark", "x": 3, "y": 2, "horizontal": false}, {"word": "octopus", "x": 9, "y": 0, "horizontal": false}, {"word": "swan", "x": 1, "y": 3, "horizontal": false}, {"word": "owl", "x": 4, "y": 5, "horizontal": false}];
    # var placement_data3 = [{"word": "street", "x": 5, "y": 10, "horizontal": true}, {"word": "bus", "x": 3, "y": 10, "horizontal": true}, {"word": "tree", "x": 6, "y": 10, "horizontal": true}, {"word": "garden", "x": 0, "y": 4, "horizontal": true}, {"word": "kitchen", "x": 0, "y": 1, "horizontal": true}, {"word": "bedroom", "x": 3, "y": 6, "horizontal": true}, {"word": "bathroom", "x": 1, "y": 2, "horizontal": true}, {"word": "playground", "x": 0, "y": 0, "horizontal": true}, {"word": "restaurant", "x": 0, "y": 9, "horizontal": true}, {"word": "bridge", "x": 0, "y": 5, "horizontal": true}, {"word": "museum", "x": 1, "y": 8, "horizontal": true}, {"word": "traffic", "x": 0, "y": 3, "horizontal": true}, {"word": "house", "x": 2, "y": 6, "horizontal": false}, {"word": "apartment", "x": 9, "y": 1, "horizontal": false}, {"word": "park", "x": 0, "y": 7, "horizontal": false}, {"word": "school", "x": 7, "y": 3, "horizontal": false}, {"word": "store", "x": 8, "y": 4, "horizontal": false}, {"word": "car", "x": 6, "y": 3, "horizontal": false}, {"word": "library", "x": 1, "y": 0, "horizontal": false}, {"word": "supermarket", "x": 10, "y": 0, "horizontal": false}];

    stats = []

    for size in range(20, 19, -1):
        for modeling_type in ("alternative", "main"):
            x_bound = size
            y_bound = size
            stage_1_start = datetime.now()
            print("Generating clauses...")
            clauses, words, possible_placements = make_problem(
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
            for solver in (Mergesat3, ):#, Mergesat3, Glucose4, MinisatGH,
                print("Solving with", solver.__name__)
                stage_2_start = datetime.now()
                placement_data = solve_problem(clauses, words, possible_placements, solver)
                stage_3_start = datetime.now()
                elapsed_time = (stage_3_start - stage_2_start).total_seconds()
                stats.append((modeling_type, len(words), size, solver.__name__, elapsed_time))
                print("Solving took ", elapsed_time, "s")

            # print("Solution:")
            # print_solution(placement_data, x_bound, y_bound)

    print(json.dumps(stats, indent=2))

    # save_solution(placement_data, words_with_hints)


if __name__ == '__main__':
    test()
