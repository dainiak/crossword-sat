from pysat.solvers import Mergesat3
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
    # clauses.extend(forbid_cells(words, is_in_hor_mode, is_x_coord, is_y_coord, [(3, 8), (6, 8), (2, 6)]))
    clauses = list(set(map(tuple, map(sorted, clauses))))
    clauses.sort()
    return clauses, words, is_in_hor_mode, is_placed, is_x_coord, is_y_coord


def solve_problem(clauses, words, is_in_hor_mode, is_placed, is_x_coord, is_y_coord):
    with Mergesat3() as solver:
        for clause in clauses:
            solver.add_clause(clause)

        if not solver.solve():
            return []

        model = solver.get_model()
        return [
            {
                "word": w,
                "x": next(x for x, vx in enumerate(is_x_coord[iw]) if vx in model),
                "y": next(y for y, vy in enumerate(is_y_coord[iw]) if vy in model),
                "horizontal": is_in_hor_mode[iw]
            }
            for iw, w in enumerate(words) if is_placed[iw] in model
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
        "corn", "rice", "bean", "chef", "menu", "fork", "spoon", "plate", "bowl", "feast", "taste", "table", "glass"
    ]

    words = [
        "elephant","giraffe","tiger","zebra","kangaroo","penguin","lion","monkey","bear","rabbit","ant","rat","bee",
        "turtle","frog","duck","fish","shark","whale","dolphin","octopus","butterfly","swan","eagle","owl","parrot","bat"
    ]

    x_bound = 11
    y_bound = 11

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

# Solving took  44.281376 s using MergeSat3
# Solution:
# f m b u r g e r p s
# r i s a l a d i a p
# u l o b o w l c s o
# i k d p l a t e t o
# t t a s t e b e a n
# c o r n f e a s t j
# h a y m e n u f a u
# e s p i z z a o b i
# f t g l a s s r l c
# s u s h i c a k e e
#


# Solving took  182.722628 s
# Solution:
# r a b b i t i g e r o
# b p e n g u i n l k c
# u d g i r a f f e a t
# t o d w e o i z p n o
# t l u h a w s e h g p
# e p c a g l h b a a u
# r h k l l i a r n r s
# f i b e e o r a t o w
# l n e m o n k e y o a
# y b a t u r t l e · n
# p a r r o t f r o g t

# [
#     {"word": "elephant", "hint": "A very large animal with grey skin, big ears that look like fans, and a long trunk."},
#     {"word": "giraffe", "hint": "The tallest animal that walks on land, with a very long neck and legs, and spots on its body."},
#     {"word": "tiger", "hint": "A big cat with orange fur and black stripes, known for its powerful build."},
#     {"word": "zebra", "hint": "Looks like a horse but with black and white stripes all over its body."},
#     {"word": "kangaroo", "hint": "An animal that hops on its hind legs and carries its baby in a pouch."},
#     {"word": "penguin", "hint": "A black and white bird that cannot fly but swims very well and lives in cold places."},
#     {"word": "lion", "hint": "Known as the 'king of the jungle,' this animal has a big mane and a loud roar."},
#     {"word": "monkey", "hint": "A playful animal that loves to climb trees and has a tail."},
#     {"word": "bear", "hint": "A large, furry animal that can stand on two legs and loves honey."},
#     {"word": "rabbit", "hint": "A small, fluffy animal with long ears and a short tail that hops."},
#     {"word": "ant", "hint": "A tiny insect that works very hard, lifting things much heavier than itself."},
#     {"word": "rat", "hint": "A small animal with a long tail, known for being clever and quick."},
#     {"word": "bee", "hint": "A small, buzzing insect that makes honey and has yellow and black stripes."},
#     {"word": "turtle", "hint": "An animal with a hard shell that it can hide inside, both on land and in water."},
#     {"word": "frog", "hint": "A small, green creature that jumps very high and says 'ribbit'."},
#     {"word": "duck", "hint": "A bird with webbed feet, good for swimming, and says 'quack'."},
#     {"word": "fish", "hint": "An animal that lives in water, breathes through gills, and has fins to swim."},
#     {"word": "shark", "hint": "A big fish with sharp teeth, known as a powerful swimmer in the ocean."},
#     {"word": "whale", "hint": "The biggest animal in the world, living in the ocean and breathing air through a blowhole."},
#     {"word": "dolphin", "hint": "A smart, friendly sea animal that can jump high out of the water and makes clicking noises."},
#     {"word": "octopus", "hint": "A sea creature with eight long arms, known for being very clever and can change color."},
#     {"word": "butterfly", "hint": "A flying insect with colorful wings and it starts life as a caterpillar."},
#     {"word": "swan", "hint": "A graceful bird with a long neck, usually white, known for swimming in lakes."},
#     {"word": "eagle", "hint": "A large bird with very good eyesight, known for flying very high."},
#     {"word": "owl", "hint": "A bird that can turn its head almost all the way around and is active at night."},
#     {"word": "parrot", "hint": "A colorful bird that can mimic sounds and words it hears."},
#     {"word": "bat", "hint": "The only mammal that can fly, known for its echo-location ability and being active at night."}
# ]
