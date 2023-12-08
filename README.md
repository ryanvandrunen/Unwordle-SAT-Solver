# CISC/CMPE 204 Modelling Project

Welcome to the major project for CISC/CMPE 204!

The goal of this project is to model a rendition of the game Wordle. Wordle is a word guessing game where a correct 5 letter word is chosen, and feedback is given on each player guess. Green tiles represent a letter in the right spot, yellow tiles represent a letter in the wrong spot, and white or grey tiles represent a letter not in the final word. The player's guesses must also be a valid word.

Our model is given a board configuration - the colours of each position in the board in a 2D array - as well as a final word, and is tasked to find all possible solutions, while displaying one possibility.

## Structure

* `documents`: Contains folders for both of your draft and final submissions. README.md files are included in both.
* `run.py`: The main driver for the project.
* `words.py`: A list of possible words that the SAT solver is given.
* `boards.py`: A list of possible boards if the user decides to have one randomly chosen.

## Team

[Madison MacNeil](https://github.com/madisonmacneil) <br />
[Simon Nair](https://github.com/Simon-Nair) <br />
[Ryan Van Drunen](https://github.com/ryanvandrunen)
