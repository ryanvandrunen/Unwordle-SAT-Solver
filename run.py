from words import WORDS

from bauhaus import Encoding, proposition, constraint, Or, And
from bauhaus.utils import count_solutions, likelihood

# These two lines make sure a faster SAT solver is used.
from nnf import config
config.sat_backend = "kissat"

# Encoding that will store all of your constraints
E = Encoding()

class Hashable:
    def __hash__(self):
        return hash(str(self))

    def __eq__(self, __value: object) -> bool:
        return hash(self) == hash(__value)

    def __repr__(self):
        return str(self)


# To create propositions, create classes for them first, annotated with "@proposition" and the Encoding
@proposition(E)
class BasicPropositions:

    def __init__(self, data):
        self.data = data

    def __repr__(self):
        return f"A.{self.data}"


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
class GreenSquare(Hashable):
    def __init__(self, x_index, y_index) -> None:
        self.x_index = x_index
        self.y_index = y_index

    def __str__(self) -> str:
        return f"Green square at ({x_index}, {y_index})"

class GreenLetter(Hashable):
    def __init__(self, letter, x_index, y_index) -> None:
        self.letter = letter
        self.x_index = x_index
        self.y_index = y_index
     
    def __str__(self) -> str:
        return f"Green {letter} at ({x_index}, {y_index})"
    
class YellowSquare(Hashable):
    def __init__(self, x_index, y_index) -> None:
        self.x_index = x_index
        self.y_index = y_index

    def __str__(self) -> str:
        return f"Yellow square at ({x_index}, {y_index})"

class YellowLetter(Hashable):
    def __init__(self, letter, x_index, y_index) -> None:
        self.letter = letter
        self.x_index = x_index
        self.y_index = y_index
     
    def __str__(self) -> str:
        return f"Yellow {letter} at ({x_index}, {y_index})"
    
class WhiteSquare(Hashable):
    def __init__(self, x_index, y_index) -> None:
        self.x_index = x_index
        self.y_index = y_index

    def __str__(self) -> str:
        return f"White square at ({x_index}, {y_index})"
    
class WhiteLetter(Hashable):
    def __init__(self, letter, x_index, y_index) -> None:
        self.letter = letter
        self.x_index = x_index
        self.y_index = y_index
     
    def __str__(self) -> str:
        return f"White {letter} at ({x_index}, {y_index})"

# Call your variables whatever you want
a = BasicPropositions("a")
b = BasicPropositions("b")   
c = BasicPropositions("c")
d = BasicPropositions("d")
e = BasicPropositions("e")
# At least one of these will be true
x = FancyPropositions("x")
y = FancyPropositions("y")
z = FancyPropositions("z")


# Build an example full theory for your setting and return it.
#
#  There should be at least 10 variables, and a sufficiently large formula to describe it (>50 operators).
#  This restriction is fairly minimal, and if there is any concern, reach out to the teaching staff to clarify
#  what the expectations are.
def example_theory():
    # Add custom constraints by creating formulas with the variables you created. 
    E.add_constraint((a | b) & ~x)
    # Implication
    E.add_constraint(y >> z)
    # Negate a formula
    E.add_constraint(~(x & y))
    # You can also add more customized "fancy" constraints. Use case: you don't want to enforce "exactly one"
    # for every instance of BasicPropositions, but you want to enforce it for a, b, and c.:
    constraint.add_exactly_one(E, a, b, c)

    return E


if __name__ == "__main__":

    T = example_theory()
    # Don't compile until you're finished adding all your constraints!
    T = T.compile()
    # After compilation (and only after), you can check some of the properties
    # of your model:
    print("\nSatisfiable: %s" % T.satisfiable())
    print("# Solutions: %d" % count_solutions(T))
    print("   Solution: %s" % T.solve())

    print("\nVariable likelihoods:")
    for v,vn in zip([a,b,c,x,y,z], 'abcxyz'):
        # Ensure that you only send these functions NNF formulas
        # Literals are compiled to NNF here
        print(" %s: %.2f" % (vn, likelihood(T, v)))
    print()
