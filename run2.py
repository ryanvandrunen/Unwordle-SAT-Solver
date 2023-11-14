from words import WORDS
COLOURS = ['Green', 'White', 'Yellow']
import pprint

from bauhaus import Encoding, proposition, constraint, Or, And
from bauhaus.utils import count_solutions, likelihood

# These two lines make sure a faster SAT solver is used.
from nnf import config

config.sat_backend = "kissat"

# Encoding that will store all of your constraints

#global vars 
E = Encoding()
ALPHABET = "abcdefghijklmnopqrstuvwxyz"
SOL = ['f','o','u','n','d']
NOTSOL = ['a', 'b', 'c', 'e', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'p', 'q', 'r', 's', 't', 'v', 'w', 'x', 'y', 'z']
BOARD = [
    ["White", "White", "White", "Yellow", "White"],
    ["White", "White", "White", "White", "Yellow"],
    ["Yellow", "White", "Yellow", "Green", "White"],
    ["Green", "Green", "Green", "Green", "Green"],
]
possible_tiles = {0: [],
                  1: [],
                  2: [],
                  3: []}
valid_tiles = [[[],[],[],[],[]],[[],[],[],[],[]],[[],[],[],[],[]], [[], [], [], [], []]]
valid_rows = [[], [], [], []]
valid_boards = []

#marker 
print("got here1")


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



for i in range(5):
    possible_tiles[3].append(Tile(3, i, BOARD[3][i], SOL[i]))
for a in ALPHABET:
    for i in range(3):
        for j in range(5):
            possible_tiles[i].append(Tile(i, j, BOARD[i][j], a))

bottom_row = Row(3, possible_tiles[3][0], possible_tiles[3][1], possible_tiles[3][2], possible_tiles[3][3], possible_tiles[3][4])

for word in WORDS:
    for row in range(2,-1,-1): 
        Row(row,word[0],word[1],word[2],word[3],word[4])

    
def build_theory():
    
    for r in range(3,-1,-1): 
        for col in range(5):
            for letter in SOL:
                if BOARD[r][col] == "Green": 
                    E.add_constraint(Tile(r,col,"Green",SOL[col]))
                    valid_tiles[r][col].append(Tile(r,col,"Green",SOL[col]))
                if BOARD[r][col] == "Yellow": 
                    E.add_constraint(~(Tile(r,col,"Yellow",SOL[col])))  
                if BOARD[r][col] == "Yellow": 
                    if letter != SOL[col]:
                        E.add_constraint(Tile(r,col,"Yellow",letter))
                        valid_tiles[r][col].append(Tile(r,col,"Yellow",letter))

    for r in range(2,-1,-1): 
        for col in range(5):
            for letter in NOTSOL: 
                if BOARD[r][col] == "Green": 
                    E.add_constraint(~(Tile(r,col,"Green",letter)))
                if BOARD[r][col] == "Yellow": 
                    E.add_constraint(~(Tile(r,col,"Yellow",letter)))
                else: 
                    E.add_constraint(Tile(r,col,"White",letter))
                    valid_tiles[r][col].append(Tile(r,col,"White",letter))

    for row in range(4):
        for let1 in valid_tiles[row][0]:
            for let2 in valid_tiles[row][1]:
                for let3 in valid_tiles[row][2]:
                    for let4 in valid_tiles[row][3]:
                        for let5 in valid_tiles[row][4]:
                            pot_word = let1.letter + let2.letter + let3.letter + let4.letter + let5.letter
                            if pot_word in WORDS:
                                E.add_constraint((
                                    (let1 & let2 & let3 & let4 & let5) & Row(row, let1, let2, let3, let4, let5)
                                ))
                                valid_rows[row].append(Row(row, let1, let2, let3, let4, let5))

    for row1 in valid_rows[0]:
        for row2 in valid_rows[1]:
            for row3 in valid_rows[2]:
                for row4 in valid_rows[3]:
                    E.add_constraint((
                        (row1 & row2 & row3 & row4) & Board(row1, row2, row3, row4)
                    ))
                    valid_boards.append(Board(row1, row2, row3, row4))


    return E

def remove_duplicates(orig_list):
    result_list = []
    for sublist in orig_list:
        temp = list(dict.fromkeys(sublist))
        result_list.append(temp)
    
    return result_list


def display_board(BOARD):
    for row in BOARD:
        print(row)

def display_solutions(sol):
    print('Possible first row words: ')
    for row in valid_rows[0]:
        word_iter = [row.letterZero.letter, row.letterOne.letter, row.letterTwo.letter, row.letterThree.letter, row.letterFour.letter]
        print(' '.join(word_iter))
    print('Possible second row words: ')
    for row in valid_rows[1]:
        word_iter = [row.letterZero.letter, row.letterOne.letter, row.letterTwo.letter, row.letterThree.letter, row.letterFour.letter]
        print(' '.join(word_iter))
    print('Possible third row words: ')
    for row in valid_rows[2]:
        word_iter = [row.letterZero.letter, row.letterOne.letter, row.letterTwo.letter, row.letterThree.letter, row.letterFour.letter]
        print(' '.join(word_iter))
    print('Possible third row words: ')
    for row in valid_rows[3]:
        word_iter = [row.letterZero.letter, row.letterOne.letter, row.letterTwo.letter, row.letterThree.letter, row.letterFour.letter]
        print(' '.join(word_iter))

if __name__ == "__main__":
    T = build_theory()
    # # Don't compile until you're finished adding all your constraints!
    T = T.compile()
    # After compilation (and only after), you can check some of the properties
    # of your model:
    print("\nSatisfiable: %s" % T.satisfiable())
    print("# Solutions: %d" % count_solutions(T))
    sol = T.solve()
    # get rid of duplicates
    valid_rows = remove_duplicates(valid_rows)
    display_solutions(sol)

    # print("\nVariable likelihoods:")
    # for v,vn in zip([a,b,c,x,y,z], 'abcxyz'):
    #     # Ensure that you only send these functions NNF formulas
    #     # Literals are compiled to NNF here
    #     print(" %s: %.2f" % (vn, likelihood(T, v)))
    # print()
    display_board(BOARD)