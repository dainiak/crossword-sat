# Crossword generator using SAT solving

## Application
This is a simple crossword generator that uses a SAT solver to construct a crossword (word grid) using a list of words. **This approach shines in case when you need a very densely filled grid**; otherwise the existing generators, e.g. [this one](https://github.com/MichaelWehar/Crossword-Layout-Generator) or [this](https://crosswordlabs.com/), are likely to be much faster.


## Example of usage
### Run in command line 
```sh
$ python3 main.py --input ./example_input.json --x_bound 11 --y_bound 9 --output output.json
```

### Example output:
```
Loaded 18 words from file example_input.json
Generating SAT constraints
Got 484518 constraints; solving SAT problem using Mergesat3…
Solving finished in 27.83336 seconds. Generated crossword:
t h e r m o m e t e r
· s p · w h i s k o ·
s c a l e · x · · v g
· i n s b l e n d e r
· s · p f o r k · n a
· s c o l a n d e r t
p o t o n g s i e v e
· r · n · p e e l e r
· s p a t u l a d l e
Solution saved to output.json
```

### The contents of `output.json`:
```json
[
  {
    "word": "spoon",
    "x": 3,
    "y": 3,
    "horizontal": false,
    "hint": "A small tool we use for stirring soup and eating cereal."
  },
  …
]
```