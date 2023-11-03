from words import WORDS
import pprint

from bauhaus import Encoding, proposition, constraint, Or, And
from bauhaus.utils import count_solutions, likelihood

# These two lines make sure a faster SAT solver is used.
from nnf import config

config.sat_backend = "kissat"

# Encoding that will store all of your constraints
E = Encoding()
ALPHABET = "abcdefghijklmnopqrstuvwxyz"
print("got here4")
SOL = ['f','o','u','n','d']
COLOURS = ['Green', 'White', 'Yellow']
class Hashable:
    def __hash__(self):
        return hash(str(self))

    def __eq__(self, __value: object) -> bool:
        return hash(self) == hash(__value)

    def __repr__(self):
        return str(self)

@proposition(E)
class Tile(Hashable):
    def __init__(self, x_index, y_index, colour, letter) -> None:
        self.x_index = x_index
        self.y_index = y_index
        self.colour = colour
        self.letter = letter

    def __str__(self) -> str:
        return f"({self.colour} {self.letter} at {self.x_index}, {self.y_index})"
    
@proposition(E)
class Word(Hashable):
    def __init__(self, word) -> None:
        self.word = word

    def __str__(self) -> str:
        return f"({self.word})"


@proposition(E)
class Row(Hashable):
    def __init__(
        self, row_number, letterZero, letterOne, letterTwo, letterThree, letterFour
    ) -> None:
        self.row_number = row_number
        self.letterZero = letterZero
        self.letterOne = letterOne
        self.letterTwo = letterTwo
        self.letterThree = letterThree
        self.letterFour = letterFour

    def __str__(self) -> str:
        return f"Row {self.row_number} contains [{self.letterZero},{self.letterOne},{self.letterTwo},{self.letterThree},{self.letterFour}]"


@proposition(E)
class Board(Hashable):
    def __init__(self, row1, row2, row3, row4) -> None:
        self.row1 = row1
        self.row2 = row2
        self.row3 = row3
        self.row4 = row4

    def __str__(self) -> str:
        return f"{self.row1} \n {self.row2} \n {self.row3} \n {self.row4}"

NOTSOL = ['a','b','c','e','g','h','i','j','k','l','m','p','q','r','s','t','v','w','x','y','z']
BOARD = [
    ["White", "White", "White", "White", "White"],
    ["White", "White", "White", "White", "Yellow"],
    ["Yellow", "White", "Yellow", "Green", "White"],
    ["Greenf", "Greeno", "Greenu", "Greenn", "Greend"],
]


# Build an example full theory for your setting and return it.
#
#  There should be at least 10 variables, and a sufficiently large formula to describe it (>50 operators).
#  This restriction is fairly minimal, and if there is any concern, reach out to the teaching staff to clarify
#  what the expectations are.
# def board_gen():
#     # Pick random word from word bank
#     word = WORDS[random.randint(0, 3835)]
#     # Generate rows
#     rows = 5 * [None], 5 * [None], 5 * [None], 5 * [None]
#     # Initialize possible colours
#     colours = ["Green", "Yellow", "White"]
#     # Fill bottom row with green tiles and letters of the random word
#     for i in range(5):
#         rows[3][i] = Tile(3, i, "Green", word[i])
#     # Iterate through rows and elements
#     for i in range(2, -1, -1):
#         for j in range(5):
#             # Pick random colour and create a tile with that colour
#             r = random.randint(0, len(colours) - 1)
#             for a in ALPHABET:
#                 possible_tiles.append(Tile(i, j, colours[r], a))
#         # Add more yellows (higher chance to generate)
#         for k in range(i):
#             colours.append("Yellow")
#         # Add more whites (higher chance to generate)
#         for l in range(i + 1):
#             colours.append("White")
#     return rows


possible_tiles = {0: [],
                  1: [],
                  2: [],
                  3: []}

for i in range(5):
    possible_tiles[3].append(Tile(3, i, BOARD[3][i][:-1], BOARD[3][i][-1:]))
for a in ALPHABET:
    for i in range(3):
        for j in range(5):
            possible_tiles[i].append(Tile(i, j, BOARD[i][j], a))

bottom_row = Row(3, possible_tiles[3][0], possible_tiles[3][1], possible_tiles[3][2], possible_tiles[3][3], possible_tiles[3][4])

def build_theory():
    print("got here2")
    # Add custom constraints by creating formulas with the variables you created.
    # E.add_constraint((a | b) & ~x)
    # # Implication
    # E.add_constraint(y >> z)
    # # Negate a formula
    # E.add_constraint(~(x & y))
    # # You can also add more customized "fancy" constraints. Use case: you don't want to enforce "exactly one"
    # # for every instance of BasicPropositions, but you want to enforce it for a, b, and c.:
    # constraint.add_exactly_one(E, a, b, c)

    i = 0 
    while i < len(BOARD[3]): 
        Tile(3,i,"Green", BOARD[3][i][-1:])
        i += 1
    # white  cannot be part of key word
    # green letter cannot also be yellow in the same column
    # green letter in some column is always green 
    row = 2
    column = 0
    while row > -1:
        while column < len(BOARD[row]):
            for letter in ALPHABET:
                E.add_constraint(
                    (
                        (Tile(3, column, "Green", letter))
                        >> ~((Tile(row, column, "White", letter)))
                    )
                )
                E.add_constraint(
                    (
                        (Tile(row, column, "Yellow", letter))
                        >> ~((Tile(row, column, "White", letter)))
                    )
                )
                E.add_constraint(
                    (
                        ~(Tile(3, column, "Green", letter))
                        | ~((Tile(row, column, "Yellow", letter)))
                    )
                )
                E.add_constraint(
                    (
                        (Tile(3, column, "Green", letter))
                        & ((Tile(row, column, "Green", letter)))
                    )
                )
            column += 1
        row -=1

    # 5 true letters = valid row
    row_solutions = [[],[],[]]
    for word in WORDS:
        for row_num in range(3, -1, -1):
            E.add_constraint((
                (Tile(row_num, 0, BOARD[row_num][0], word[0]))
                & (Tile(row_num, 1, BOARD[row_num][1], word[1]))
                & (Tile(row_num, 2, BOARD[row_num][2], word[2]))
                & (Tile(row_num, 3, BOARD[row_num][3], word[3]))
                & (Tile(row_num, 4, BOARD[row_num][4], word[4]))
            ) & (
                Row(
                    row_num,
                    (Tile(row_num, 0, BOARD[row_num][0], word[0])),
                    (Tile(row_num, 1, BOARD[row_num][1], word[1])),
                    (Tile(row_num, 2, BOARD[row_num][2], word[2])),
                    (Tile(row_num, 3, BOARD[row_num][3], word[3])),
                    (Tile(row_num, 4, BOARD[row_num][4], word[4])),
                )
            ))
            if (row_num != 3):
                row_solutions[row_num].append(Row(
                        row_num,
                        (Tile(row_num, 0, BOARD[row_num][0], word[0])),
                        (Tile(row_num, 1, BOARD[row_num][1], word[1])),
                        (Tile(row_num, 2, BOARD[row_num][2], word[2])),
                        (Tile(row_num, 3, BOARD[row_num][3], word[3])),
                        (Tile(row_num, 4, BOARD[row_num][4], word[4])),
                    ))

    for solutions in row_solutions: 
        constraint.add_exactly_one(E,[row_solutions[0][i]for num in range(3)])
    # white letter can only be on the board once

    for letter in ALPHABET:
        for row1 in range(3):
            for row2 in range(3):
                for i in range(5):
                    for j in range(5):
                        if row1 != row2:
                            E.add_constraint(~(Tile(row1, i, "White", letter) & Tile(row2, j, "White", letter)))



    # letter can't be green and yellow in the same row 
    # green(3, 0, a) >> green(2, 0, a)
    #exactly one colour at s
    
    # cant guess the same word
    for word in WORDS: 
        for row1 in range(4):
            for row2 in range(4):
                if row1 != row2:
                    E.add_constraint(~((Row(row1, word[0],word[1],word[2],word[3],word[4])) & (Row(row2, word[0],word[1],word[2],word[3],word[4]))))


    #4 valid rows = SOLUTION YAYAYAYAYYYYYY
    i = 0
    j = 0
    k = 0
    while i < len(row_solutions[0]):
        while j < len(row_solutions[1]): 
            while k < len(row_solutions[2]):
                E.add_constraint((row_solutions[0][i] & row_solutions[1][j] & row_solutions[2][k]) >> Board(row_solutions[0][i], row_solutions[1][j], row_solutions[2][k], bottom_row) )
            j+=1
        i+=1

    return E

def display_board(board):
    for row in board:
        print(row)

def display_solutions(sol):
    display_rows(sol)

def display_rows(sol): 
    print(len(row_solutions[0]))
    print(len(row_solutions[1]))
    print(len(row_solutions[2]))
    print(Board(row_solutions[0][0], row_solutions[1][1], row_solutions[2][0], bottom_row))
    for i in range (len(row_solutions[0])): 
        print("i:", i)
        for j in range (len(row_solutions[1])):
            print("j:", j)
            for k in range (len(row_solutions[2])):
                if sol[Board(row_solutions[0][i], row_solutions[1][j], row_solutions[2][k], bottom_row)]: 
                    print(Board(row_solutions[0][i], row_solutions[1][j], row_solutions[2][k], bottom_row))

if __name__ == "__main__":
    T = build_theory()
    print("got here3")

    # # Don't compile until you're finished adding all your constraints!
    T = T.compile()
    # E.introspect()
    # After compilation (and only after), you can check some of the properties
    # of your model:
    print("got here4")
    print("\nSatisfiable: %s" % T.satisfiable())
    print("# Solutions: %d" % count_solutions(T))
    sol = T.solve()
    display_solutions(sol)
    print("\nSatisfiable: %s" % T.satisfiable())
    print("# Solutions: %d" % count_solutions(T))

    # print("\nVariable likelihoods:")
    # for v,vn in zip([a,b,c,x,y,z], 'abcxyz'):
    #     # Ensure that you only send these functions NNF formulas
    #     # Literals are compiled to NNF here
    #     print(" %s: %.2f" % (vn, likelihood(T, v)))
    # print()
    display_board(BOARD)