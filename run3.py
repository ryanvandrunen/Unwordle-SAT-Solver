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
SOL = ['b', 'l', 'o', 't', 's']
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
# def get_board(): 
#     board_full = False 
#     row_num = 1 
#     while board_full == False: 
#         row = input('In the form ["White", "Green", "Yellow", "White", "White"], \n Please input row ', row_num, ": ")
#         if 

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

# Proposition for a Tile, holds row and column index, and colour
@proposition(E)
class Tile(Hashable):
    def __init__(self, x_index, y_index, colour) -> None:
        self.x_index = x_index
        self.y_index = y_index
        self.colour = colour

    def __str__(self) -> str:
        return f"({self.colour} at {self.x_index}, {self.y_index})"

# Proposition for a Letter, holds row and column index, letter and colour
@proposition(E)
class Letter(Hashable):
    def __init__(self, x_index, y_index, letter, colour) -> None:
        self.x_index = x_index
        self.y_index = y_index
        self.letter = letter
        self.colour = colour

    def __str__(self) -> str:
        return f"({self.colour} {self.letter} at {self.x_index}, {self.y_index})"

# Proposition for a Row, holds row number (0-3) and the 5 letters it contains
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
            # If the letter is in this spot in the solution, it must be green
            if letter == SOL[col]: 
                E.add_constraint((Letter(3,col,letter,"Green")))
            # If the letter is not in this spot in the solution, it cannot be green
            else: 
                E.add_constraint(~(Letter(3,col,letter,"Green")))

    # For each letter in the first 3 rows
    for r, col in itertools.product(range(2, -1, -1), range(5)):
        for letter in ALPHABET:
            # A green letter in any row implies a green letter in the same column in the solution row
            E.add_constraint((Letter(r,col, letter, "Green" )) >> (Letter(3,col, letter, "Green" )))
            # A green letter in the solution row implies that the letter cannot be yellow in the same column in any other row
            E.add_constraint((Letter(3,col, letter, "Green") >> ~Letter(r,col, letter, "Yellow")))

    # For each letter in each row
    for r, col in itertools.product(range(3,-1,-1), range(5)):
        for letter in ALPHABET:
            # A yellow letter in any position implies that it must be present in the solution row
            E.add_constraint((Letter(r,col, letter, "Yellow")) >> 
                                            (Letter(3,0,letter,"Green")| Letter (3,1,letter,"Green") |
                                            Letter(3,2,letter,"Green") |Letter(3,3,letter,"Green")|
                                            Letter(3,4,letter,"Green")))
            # For each position in the solution row
            for col2 in range(5):
                # A white letter at any position implies that it cannot be present in the solution row
                E.add_constraint((Letter(r,col, letter, "White")) >> ~(Letter(3,col2,letter,"Green")))
            # For each colour (white, yellow, green)
            for colour in COLOURS:
                # If the board configuration at a position is not the current colour
                if BOARD[r][col] != colour: 
                    # That letter at that position cannot be the current colour
                    E.add_constraint(~(Tile(r,col,colour)))
                # A letter at any position with the current colour implies that the tile at that position is the same colour
                E.add_constraint(((Letter(r,col,letter, colour)) >> (Tile(r,col,colour))))

    return E


def build_theory2(arr,vRows,vBoards):

    for row in range(3):
        # Generate combinations of valid tiles for each row
        combinations = itertools.product(*arr[row])
        for combo in combinations:
            # If the combination of valid letters is in the word list
            pot_word = ''.join(letter.letter for letter in combo)
            if pot_word in WORDS:
                # The 5 letters imply a row at the given index
                E.add_constraint(And(*combo) >> Row(row, *combo))
                # Add it to valid rows list
                vRows[row].add(Row(row, *combo))

    vRows[3].add(Row(4, Letter(3, 0, SOL[0], 'Green'), Letter(3, 1, SOL[1], 'Green'), Letter(3, 2, SOL[2], 'Green'), Letter(3, 3, SOL[3], 'Green'), Letter(3, 4, SOL[4], 'Green')))

    # Generate combinations of valid rows
    combinations = itertools.product(vRows[0], vRows[1], vRows[2], vRows[3])
    for combo in combinations:
        # For every combination, the rows imply a board solution
        E.add_constraint(And(*combo) >> Board(*combo))
        # Add the board to valid boarrds list
        vBoards.add(Board(*combo))

    return E

def display_board(BOARD):
    # For each row in the board
    row_iter = [BOARD.row1, BOARD.row2, BOARD.row3, BOARD.row4]
    for row in row_iter:
        # Create letter and colour (converted to uppercase for colorama) iteration list
        letter_iter = [row.letterZero.letter, row.letterOne.letter, row.letterTwo.letter, row.letterThree.letter, row.letterFour.letter]
        colour_iter = [row.letterZero.colour.upper(), row.letterOne.colour.upper(), row.letterTwo.colour.upper(), row.letterThree.colour.upper(), row.letterFour.colour.upper()]
        # For each letter in the row
        for i in range(len(letter_iter)):
            # If the colour is green then print it as green
            if colour_iter[i] == "GREEN":
                print(Fore.GREEN + f'{letter_iter[i]} ', end="")
            # If the colour is yellow then print it as yellow
            elif colour_iter[i] == "YELLOW":
                print(Fore.YELLOW + f'{letter_iter[i]} ', end="")
            # If the colour is white then print it as white
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

# def get_board(): 
#     print("Welcome to UNWORDLE!")
#     decision = input("Would you like to provide a board for the model or have one randomly generated?",
#                      "\nPlease enter P to provide a board or R to have a board randomly generated for you" )
#     while input != 'P' or input != 'R': 
#         print("Oops! The input you entered was not a valid choice. Please try again: ")
#         decision = input("Would you like to provide a board for the model or have one randomly generated? (P/R)" )
#     if input == 'P': 
        
# def get_row(num): 
#     row = input("Please input row ",num ,": ")

if __name__ == "__main__":
    # Keep track of time elapsed
    start = time.time()
    print(f"The final word is: {''.join(SOL)}")
    # If the word is not 5 letters then raise exception
    if len(SOL) != 5: 
        raise Exception("Final word is not 5 letters.")
    # Compile the build theory
    T = build_theory()
    T = T.compile()
    sol = T.solve()
    # For every true letter proposition, add it to a set
    for r, col in itertools.product(range(3, -1, -1), range(5)):
        for colour in COLOURS: 
            for letter in ALPHABET: 
                if sol[Letter(r,col,letter, colour)]:
                    valid_tiles[r][col].add(Letter(r,col,letter, colour))
    # Compile the 2nd build theory to create row and board constraints
    J = build_theory2(valid_tiles,valid_rows,valid_boards)
    J = J.compile()
    print("Satisfiable: %s" % J.satisfiable())
    sol = J.solve()
    # Use list comprehension to get only the board solutions
    board_sol = []
    [board_sol.append(item) for item in sol if hasattr(item, "row1")]
    display_solutions(board_sol)
    # Stop time and print elapsed time
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