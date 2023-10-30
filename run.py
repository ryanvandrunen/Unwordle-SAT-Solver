from words import WORDS
import random

from bauhaus import Encoding, proposition, constraint, Or, And
from bauhaus.utils import count_solutions, likelihood

# These two lines make sure a faster SAT solver is used.
from nnf import config

config.sat_backend = "kissat"

# Encoding that will store all of your constraints
E = Encoding()
ALPHABET = "abcdefghijklmnopqrstuvwxyz"


class Hashable:
    def __hash__(self):
        return hash(str(self))

    def __eq__(self, __value: object) -> bool:
        return hash(self) == hash(__value)

    def __repr__(self):
        return str(self)


# Different classes for propositions are useful because this allows for more dynamic constraint creation
# for propositions within that class. For example, you can enforce that "at least one" of the propositions
# that are instances of this class must be true by using a @constraint decorator.
# other options include: at most one, exactly one, at most k, and implies all.
# For a complete module reference, see https://bauhaus.readthedocs.io/en/latest/bauhaus.html
@constraint.at_least_one(E)
@proposition(E)
class FancyPropositions:
    def __init__(self, data):
        self.data = data

    def __repr__(self):
        return f"A.{self.data}"


@proposition(E)
class Letter(Hashable):
    def __init__(self, letter) -> None:
        self.letter = letter

    def __str__(self) -> str:
        return f"{self.letter}"


@proposition(E)
class Colour(Hashable):
    def __init__(self, colour) -> None:
        self.colour = colour

    def __str__(self) -> str:
        return f"{self.colour}"


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
class Assigned(Hashable):
    def __init__(self, tile, letter) -> None:
        self.tile = tile
        self.letter = letter

    def __str__(self) -> str:
        return f"{self.letter} at {self.tile})"


@proposition(E)
class Row(Hashable):
    def __init__(self, row_number, letters) -> None:
        self.row_number = row_number
        self.letters = letters

    def __str__(self) -> str:
        return f"Row {self.row_number} contains {self.letters}"


@proposition(E)
class Board(Hashable):
    def __init__(self, rows) -> None:
        self.rows = rows

    def __str__(self) -> str:
        return f"{self.rows[0]} \n {self.rows[1]} \n {self.rows[2]} \n {self.rows[3]}"


# Build an example full theory for your setting and return it.
#
#  There should be at least 10 variables, and a sufficiently large formula to describe it (>50 operators).
#  This restriction is fairly minimal, and if there is any concern, reach out to the teaching staff to clarify
#  what the expectations are.

def board_gen():
    # Pick random word from word bank
    word = WORDS[random.randint(0, 3835)]
    # Generate rows
    rows = 5 * [None], 5 * [None], 5 * [None], 5 * [None]
    # Initialize possible colours
    colours = ["Green", "Yellow", "White"]
    # Fill bottom row with green tiles and letters of the random word
    for i in range(5):
        rows[3][i] = Tile(3, i, "Green", word[i])
    # Iterate through rows and elements
    for i in range(2, -1, -1):
        for j in range(5):
            # Pick random colour and create a tile with that colour
            r = random.randint(0, len(colours)-1)
            rows[i][j] = Tile(i, j, colours[r], None)
        # Add more yellows (higher chance to generate)
        for k in range(i):
            colours.append("Yellow")
        # Add more whites (higher chance to generate)
        for l in range(i + 1):
            colours.append("White")
    return rows


def display_board(board):
    for row in board:
        print(row)

BOARD = board_gen()

def build_theory(): 
    # Add custom constraints by creating formulas with the variables you created. 
    # E.add_constraint((a | b) & ~x)
    # # Implication
    # E.add_constraint(y >> z)
    # # Negate a formula
    # E.add_constraint(~(x & y))
    # # You can also add more customized "fancy" constraints. Use case: you don't want to enforce "exactly one"
    # # for every instance of BasicPropositions, but you want to enforce it for a, b, and c.:
    # constraint.add_exactly_one(E, a, b, c)
    for a in ALPHABET:
        for r in BOARD:
            for t in r:
                if (t.x_index != 3):
                    t.letter = ALPHABET



    return E


if __name__ == "__main__":
    T = build_theory()
    # # Don't compile until you're finished adding all your constraints!
    # T = T.compile()
    # After compilation (and only after), you can check some of the properties
    # of your model:
    # print("\nSatisfiable: %s" % T.satisfiable())
    # print("# Solutions: %d" % count_solutions(T))
    # print("   Solution: %s" % T.solve())

    # print("\nVariable likelihoods:")
    # for v,vn in zip([a,b,c,x,y,z], 'abcxyz'):
    #     # Ensure that you only send these functions NNF formulas
    #     # Literals are compiled to NNF here
    #     print(" %s: %.2f" % (vn, likelihood(T, v)))
    # print()
    display_board(BOARD)
