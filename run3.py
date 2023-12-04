from words import WORDS
import random, time, itertools

from colorama import Fore, init
init(autoreset=True)

from bauhaus import Encoding, proposition, constraint, Or, And
from bauhaus.utils import count_solutions, likelihood

# These two lines make sure a faster SAT solver is used.
from nnf import config

config.sat_backend = "kissat"

# Encoding that will store all of your constraints

#global vars 
E = Encoding()
ALPHABET = "abcdefghijklmnopqrstuvwxyz"
# Pick a random word from words.py and split it into a list of characters
SOL = list(WORDS[random.randint(0, len(WORDS)-1)])
# Generate a list of all the characters not used in the solution
NOTSOL = [letter for letter in ALPHABET if letter not in SOL]
# Give a valid colour layout to the SAT solver
COLOURS = ["Green", "White", "Yellow"]
BOARD = [
    ["White", "Green", "Yellow", "White", "White"],
    ["Yellow", "Green", "White", "White", "White"],
    ["White", "Green", "White", "Yellow", "White"],
    ["Green", "Green", "Green", "Green", "Green"],
]
valid_tiles = [[set(),set(),set(),set(),set()],[set(),set(),set(),set(),set()],[set(),set(),set(),set(),set()], [set(), set(), set(), set(), set()]]
valid_rows = [set(), set(), set(), set()]
valid_boards = set()


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

# Proposition for a Tile, holds row, column index, colour and letter
@proposition(E)
class Tile(Hashable):
    def __init__(self, x_index, y_index, colour) -> None:
        self.x_index = x_index
        self.y_index = y_index
        self.colour = colour

    def __str__(self) -> str:
        return f"({self.colour} at {self.x_index}, {self.y_index})"

@proposition(E)
class Letter(Hashable):
    def __init__(self, x_index, y_index, letter, colour) -> None:
        self.x_index = x_index
        self.y_index = y_index
        self.letter = letter
        self.colour = colour

    def __str__(self) -> str:
        return f"({self.colour} {self.letter} at {self.x_index}, {self.y_index})"

# Proposition for a Row, holds row number (0-3) and the 5 tiles it contains
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

# Proposition for a Board, holds the 4 rows it contains
@proposition(E)
class Board(Hashable):
    def __init__(self, row1, row2, row3, row4) -> None:
        self.row1 = row1
        self.row2 = row2
        self.row3 = row3
        self.row4 = row4

    def __str__(self) -> str:
        return f"{self.row1} \n {self.row2} \n {self.row3} \n {self.row4}"

def build_theory():

    for col in range(5):
        for letter in ALPHABET: 
            if letter == SOL[col]: 
                E.add_constraint((Letter(3,col,letter,"Green")))
            else: 
                E.add_constraint(~(Letter(3,col,letter,"Green")))

    for r, col in itertools.product(range(2, -1, -1), range(5)):
        for letter in ALPHABET:
            E.add_constraint((Letter(r,col, letter, "Green" )) >> (Letter(3,col, letter, "Green" )))
            E.add_constraint((Letter(3,col, letter, "Green") >> ~Letter(r,col, letter, "Yellow")))

    for r, col in itertools.product(range(3,-1,-1), range(5)):
        for letter in ALPHABET:
            E.add_constraint((Letter(r,col, letter, "Yellow")) >> 
                                            (Letter(3,0,letter,"Green")| Letter (3,1,letter,"Green") |
                                            Letter(3,2,letter,"Green") |Letter(3,3,letter,"Green")|
                                            Letter(3,4,letter,"Green")))
            for col2 in range(5):
                E.add_constraint((Letter(r,col, letter, "White")) >> ~(Letter(3,col2,letter,"Green")))
            for colour in COLOURS:
                if BOARD[r][col] != colour: 
                    E.add_constraint(~(Tile(r,col,colour)))
                E.add_constraint(((Letter(r,col,letter, colour)) >> (Tile(r,col,colour))))

    return E


def build_theory2(arr,vRows,vBoards):

    for row in range(3):
        # Generate combinations of valid tiles for each row
        combinations = itertools.product(*arr[row])
        for combo in combinations:
            pot_word = ''.join(letter.letter for letter in combo)
            if pot_word in WORDS:
                # Create a constraint for the combination and add it
                E.add_constraint(And(*combo) & Row(row, *combo))
                vRows[row].add(Row(row, *combo))

    vRows[3].add(Row(4, Letter(3, 0, SOL[0], 'Green'), Letter(3, 1, SOL[1], 'Green'), Letter(3, 2, SOL[2], 'Green'), Letter(3, 3, SOL[3], 'Green'), Letter(3, 4, SOL[4], 'Green')))

    combinations = itertools.product(vRows[0], vRows[1], vRows[2], vRows[3])
    for combo in combinations:
        E.add_constraint(And(*combo) & Board(*combo))
        vBoards.add(Board(*combo))

    return E

def display_board(BOARD):
    # For each row in the board
    row_iter = [BOARD.row1, BOARD.row2, BOARD.row3, BOARD.row4]
    for row in row_iter:
        # Print the letters of each row in the board separated by a space
        letter_iter = [row.letterZero.letter, row.letterOne.letter, row.letterTwo.letter, row.letterThree.letter, row.letterFour.letter]
        colour_iter = [row.letterZero.colour.upper(), row.letterOne.colour.upper(), row.letterTwo.colour.upper(), row.letterThree.colour.upper(), row.letterFour.colour.upper()]
        for i in range(len(letter_iter)):
            if colour_iter[i] == "GREEN":
                print(Fore.GREEN + f'{letter_iter[i]} ', end="")
            elif colour_iter[i] == "YELLOW":
                print(Fore.YELLOW + f'{letter_iter[i]} ', end="")
            else:
                print(Fore.WHITE + f'{letter_iter[i]} ', end="")
        print('\n', end="")
        
def display_solutions(sol):
    num_sol = len(sol)
    # If there are 0 board solutions, we cannot display a board
    print(f"Board Solutions: %d" % num_sol)
    if num_sol == 0:
        print('No valid boards to display.')
    else: 
        # If there are board solutions, pick a random one and display it
        sol_list = list(sol)
        print('Possible solution:')
        display_board(random.choice(sol_list))

if __name__ == "__main__":
    start = time.time()
    print(f"The final word is: {''.join(SOL)}")
    if len(SOL) > 5: 
        raise Exception("Final word is greater than 5.")
    T = build_theory()
    T = T.compile()
    sol = T.solve()
    for r, col in itertools.product(range(3, -1, -1), range(5)):
        for colour in COLOURS: 
            for letter in ALPHABET: 
                if sol[Letter(r,col,letter, colour)]:
                    valid_tiles[r][col].add(Letter(r,col,letter, colour))
    J = build_theory2(valid_tiles,valid_rows,valid_boards)
    J = J.compile()
    print("Satisfiable: %s" % J.satisfiable())
    sol = J.solve()
    print('here')
    unique_sol = set()
    [unique_sol.add(item) for item in sol if hasattr(item, "row1")]
    display_solutions(unique_sol)
    end = time.time()
    elapsed = round(end-start, 2)
    print(f'Compile time of {elapsed} seconds.\n')

# Board with 1190 solutions and length 1000 word list takes ~1m30s
# Board with 480 solutions and length 1000 word list takes ~20s
# Board with 816 solutions and length 2000 word list takes ~20s
# Board with 1300 solutions and length 2000 word list takes ~50s
# Board with 336 solutions and length 3834 word list takes ~1m20s
# Board with 2392 solutions and length 2000 word list takes ~5m15s

# To make our constraints simpler, we decided that hints do not have to be reused
# e.g. a Yellow Y in the first row does not constrain that a Y must be included in the second row.
# We also decided that white letters can be reused across the board
# e.g. a White K is guessed in the first row does not constrain that it cannot be guessed in the second row

# Maximum length word list (3834) and a board with many solutions (>1000) takes too long to compute
# Limit the word list, right now it's at 2000 words and has a reasonable runtime

# One of the major hurdles we overcame was runtime. When keeping track of valid tiles, rows, and boards, lots 
# of duplicate propositions and constraints were being generated. To fix this issue, and massively 
# optimize our project, we checked if a proposition was not already in the list before adding it.
# At first, a board and word that resulted in single-digit solutions would get 'Killed' by the docker container.
# After implementing these changes, it would compile in seconds. Even a board and word that resulted in 
# over a thousand solutions took less than a minute to compile.