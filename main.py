from itertools import combinations, product

words: list[str] = [
    "pizza",
    "cake",
    "juice",
    "soda",
    "burger",
    "salad",
    "toast",
    "fruit",
    "sushi",
    "pasta",
    "milk",
    "corn",
    "rice",
    "bean",
    "chef",
    "menu",
    "fork",
    "spoon",
    "plate",
    "bowl",
    "feast",
    "taste"
]

counter = 1
x_bound = 10
y_bound = 10

is_in_hor_mode = [True] * len(words) + [False] * len(words)

words = words + words

is_x_coord = [[] for _ in range(len(words))]
is_y_coord = [[] for _ in range(len(words))]

clauses = []
crossing_vars = []

for iw, w in enumerate(words):
    for x in range(x_bound + ((1 - len(w)) if is_in_hor_mode[iw] else 0)):
        is_x_coord[iw].append(counter)
        counter += 1
    for y in range(y_bound + ((1 - len(w)) if not is_in_hor_mode[iw] else 0)):
        is_y_coord[iw].append(counter)
        counter += 1

for (iw1, w1), (iw2, w2) in combinations(enumerate(words), 2):
    if iw1 == iw2:
        continue
    for (x1, vx1), (y1, vy1), (x2, vx2), (y2, vy2) in product(enumerate(is_x_coord[iw1]), enumerate(is_y_coord[iw1]),
                                                              enumerate(is_x_coord[iw2]), enumerate(is_y_coord[iw2])):
        if (
                is_in_hor_mode[iw1] and is_in_hor_mode[iw2] and y1 == y2 and (
                x1 <= x2 < x1 + len(w1) or x2 <= x1 < x2 + len(w2))
                or
                not is_in_hor_mode[iw1] and not is_in_hor_mode[iw2] and x1 == x2 and (
                y1 <= y2 < y1 + len(w1) or y2 <= y1 < y2 + len(w2))
        ):
            clauses.append([-vx1, -vy1, -vx2, -vy2])

        if is_in_hor_mode[iw1] and not is_in_hor_mode[iw2] and x1 <= x2 < x1 + len(w1) and y2 <= y1 < y2 + len(w2):
            if w1[x2 - x1] != w2[y1 - y2]:
                clauses.append([-vx1, -vy1, -vx2, -vy2])
            # else:
            #     clauses.append([-vx1, -vx2, -vy1, -vy2, counter])
            #     crossing_vars.append(counter)
            #     counter += 1
        if not is_in_hor_mode[iw1] and is_in_hor_mode[iw2] and y1 <= y2 < y1 + len(w1) and x2 <= x1 < x2 + len(w2):
            if w1[y2 - y1] != w2[x1 - x2]:
                clauses.append([-vx1, -vy1, -vx2, -vy2])
            # else:
            #     clauses.append([-vx1, -vx2, -vy1, -vy2, counter])
            #     crossing_vars.append(counter)
            #     counter += 1

is_placed = []
for iw in range(len(words)):
    is_placed.append(counter)
    counter += 1
    clauses.append([-is_placed[iw]] + is_x_coord[iw])
    clauses.append([-is_placed[iw]] + is_y_coord[iw])

for (iw1, w1), (iw2, w2) in combinations(enumerate(words), 2):
    if w1 == w2 and is_in_hor_mode[iw1] != is_in_hor_mode[iw2]:
        clauses.append([is_placed[iw1], is_placed[iw2]])
        clauses.append([-is_placed[iw1], -is_placed[iw2]])

# forbidden_cells = [(4, 5), (6, 8)]
forbidden_cells = [(3, 8), (6, 8), (2, 6)]
# forbidden_cells = []

for x, y in forbidden_cells:
    for iw, w in enumerate(words):
        for xw, vxw in enumerate(is_x_coord[iw]):
            for yw, vyw in enumerate(is_y_coord[iw]):
                if is_in_hor_mode[iw] and xw <= x < xw + len(w) and yw == y or not is_in_hor_mode[
                    iw] and yw <= y < yw + len(w) and xw == x:
                    clauses.append([-vxw, -vyw])

from pysat.formula import CNF
from pysat.solvers import Solver

cnf = CNF(from_clauses=clauses)

placement_data = []

# with Solver(bootstrap_with=cnf) as solver:
#     result = solver.solve()
#     print('formula is', f'{"" if result else "un"}satisfiable')
#     if result:
#         model = set(solver.get_model())

#         for iw, w in enumerate(words):
#             if is_placed[iw] not in model:
#                 continue
#             for x, vx in enumerate(is_x_coord[iw]):
#                 if vx in model:
#                     set_x = x
#                     break
#             else:
#                 assert False
#             for y, vy in enumerate(is_y_coord[iw]):
#                 if vy in model:
#                     set_y = y
#                     break
#             else:
#                 assert False
#             placement_data.append(
#                 {
#                     "word": w,
#                     "x": set_x,
#                     "y": set_y,
#                     "horizontal": is_in_hor_mode[iw]
#                 }
#             )

from pycryptosat import Solver

s = Solver()
for clause in clauses:
    s.add_clause(clause)

sat, solution = s.solve()
print('formula is', f'{"" if sat else "un"}satisfiable')
if sat:
    for iw, w in enumerate(words):
        if not solution[is_placed[iw]]:
            continue
        for x, vx in enumerate(is_x_coord[iw]):
            if solution[vx]:
                set_x = x
                break
        else:
            assert False
        for y, vy in enumerate(is_y_coord[iw]):
            if solution[vy]:
                set_y = y
                break
        else:
            assert False
        placement_data.append(
            {
                "word": w,
                "x": set_x,
                "y": set_y,
                "horizontal": is_in_hor_mode[iw]
            }
        )
