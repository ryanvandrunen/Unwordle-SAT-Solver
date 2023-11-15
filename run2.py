from words import WORDS
import random

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
SOL = [x for x in WORDS[random.randint(0, len(WORDS)-1)]]
# Generate a list of all the characters not used in the solution
NOTSOL = [letter for letter in ALPHABET if letter not in SOL]
# Give a valid colour layout to the SAT solver
BOARD = [
    ["White", "Green", "Yellow", "White", "White"],
    ["Yellow", "Green", "White", "White", "White"],
    ["White", "Green", "White", "Yellow", "White"],
    ["Green", "Green", "Green", "Green", "Green"],
]
valid_tiles = [[[],[],[],[],[]],[[],[],[],[],[]],[[],[],[],[],[]], [[], [], [], [], []]]
valid_rows = [[], [], [], []]
valid_boards = []


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
    def __init__(self, x_index, y_index, colour, letter) -> None:
        self.x_index = x_index
        self.y_index = y_index
        self.colour = colour
        self.letter = letter

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
    
    # Iterate through every tile on the board and every letter in the final word
    for r in range(3,-1,-1): 
        for col in range(5):
            for letter in SOL:
                # If the tile must be green, add a constraint that the Tile at that index must be a Green tile
                # with the letter from that column of the final word
                if BOARD[r][col] == "Green": 
                    E.add_constraint(Tile(r,col,"Green",SOL[col]))
                    if (Tile(r, col, "Green", SOL[col]) not in valid_tiles[r][col]):
                        valid_tiles[r][col].append(Tile(r,col,"Green",SOL[col]))
                # If the tile must be yellow, 
                if BOARD[r][col] == "Yellow": 
                    E.add_constraint(~(Tile(r,col,"Yellow",SOL[col])))  
                if BOARD[r][col] == "Yellow": 
                    if letter != SOL[col]:
                        E.add_constraint(Tile(r,col,"Yellow",letter))
                        if (Tile(r, col, "Yellow", letter) not in valid_tiles[r][col]):
                            valid_tiles[r][col].append(Tile(r,col,"Yellow",letter))

    # Iterate through every tile on the board and every letter not in the final word
    for r in range(2,-1,-1): 
        for col in range(5):
            for letter in NOTSOL: 
                # The letter at any index cannot be a Green or Yellow tile
                E.add_constraint(~(Tile(r,col,"Green",letter)))
                E.add_constraint(~(Tile(r,col,"Yellow",letter)))
                # If the index must be White, then any letter not in the solution 
                # is a valid tile at that index
                if BOARD[r][col] == "White":
                    E.add_constraint(Tile(r,col,"White",letter))
                    if (Tile(r, col, "White", letter) not in valid_tiles[r][col]):
                        valid_tiles[r][col].append(Tile(r,col,"White",letter))

    # For every valid tile that we gathered
    for row in range(4):
        for let1 in valid_tiles[row][0]:
            for let2 in valid_tiles[row][1]:
                for let3 in valid_tiles[row][2]:
                    for let4 in valid_tiles[row][3]:
                        for let5 in valid_tiles[row][4]:
                            # If the letters of all 5 tiles are in the word list
                            # Add a constraint that all the letters and the row of the letters must be true
                            # Add the row to the list of valid rows at the row index
                            pot_word = let1.letter + let2.letter + let3.letter + let4.letter + let5.letter
                            if pot_word in WORDS:
                                E.add_constraint((
                                    (let1 & let2 & let3 & let4 & let5) & Row(row, let1, let2, let3, let4, let5)
                                ))
                                if (Row(row, let1, let2, let3, let4, let5) not in valid_rows[row]):
                                    valid_rows[row].append(Row(row, let1, let2, let3, let4, let5))

    # For every valid row that we gathered
    for row1 in valid_rows[0]:
        for row2 in valid_rows[1]:
            for row3 in valid_rows[2]:
                for row4 in valid_rows[3]:
                    # Add a constraint that each row and the board must be true
                    # Add the board to the list of valid boards
                    E.add_constraint((
                        (row1 & row2 & row3 & row4) & Board(row1, row2, row3, row4)
                    ))
                    if (Board(row1, row2, row3, row4) not in valid_boards):
                        valid_boards.append(Board(row1, row2, row3, row4))

    return E

def display_board(BOARD):
    # For each row in the board
    row_iter = [BOARD.row1, BOARD.row2, BOARD.row3, BOARD.row4]
    for row in row_iter:
        # Print the letters of each row in the board separated by a space
        letter_iter = [row.letterZero.letter, row.letterOne.letter, row.letterTwo.letter, row.letterThree.letter, row.letterFour.letter]
        print(' '.join(letter_iter))

def display_solutions(sol):
    num_sol = len(sol)
    # If there are 0 board solutions, we cannot display a board
    print(f"Board Solutions: %d" % num_sol)
    if num_sol == 0:
        print('No valid boards to display.')
    else: 
        # If there are board solutions, pick a random one and display it
        print('Possible solution:')
        display_board(sol[random.randint(0, len(sol)-1)])

if __name__ == "__main__":
    print(f"The final word is: {''.join(SOL)}")
    if len(SOL) > 5: 
        raise Exception("Final word is greater than 5.")
    T = build_theory()
    T = T.compile()
    print("Satisfiable: %s" % T.satisfiable())
    sol = T.solve()
    unique_sol = []
    [unique_sol.append(item) for item in sol if item not in unique_sol and hasattr(item, "row1")]
    display_solutions(unique_sol)

# Get screenshot of docker container being killed after long time