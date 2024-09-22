# SAT-based crossword generator

## Application
This is a simple crossword generator that uses a SAT solver to construct a crossword (word grid) using a list of words. **This approach shines in case when you need a very densely filled grid**; otherwise the existing generators, e.g. [this one](https://github.com/MichaelWehar/Crossword-Layout-Generator) or [this](https://crosswordlabs.com/), are likely to be much faster.

## Usage

```bash
python crossword_generator.py --x_bound <width> --y_bound <height> --words <words> [--options <options_file>] [--solver <solver_name>] [--input <input_file>] [--output <output_file>] [--connected]
```

**Required arguments:**

* `--x_bound`: Width of the crossword grid.
* `--y_bound`: Height of the crossword grid.

**Optional arguments:**
* `--words`: Comma-separated list of words or path to a JSON file containing words and hints.
* `--input`: Path to a JSON file containing words and hints. If provided, overrides `--words`.
* `--options`: Path to a JSON file containing crossword options (see below).
* `--solver`: Name of the SAT solver to use. One of `Glucose`, `Mergesat`, `Lingeling`, `MinisatGH`, `CryptoMinisat`. Default is `Mergesat`.
* `--output`: Path to a file where the solution will be saved as JSON.
* `--connected`: If set to `True`, requires the crossword to be connected (all words must be connected by intersections). Default is `True`.

### Input Formats

#### Words

* **Comma-separated list:**  Provide a comma-separated list of words on the command line using the `--words` argument.
* **JSON file:** Create a JSON file with a list of words, optionally including hints. Each word can be a string or a dictionary with keys `word` and `hint`.

```json
[
  "hello",
  "world",
  {"word": "python", "hint": "A popular programming language"},
  "coding"
]
```

#### Options
*JSON file:* Create a JSON file with the following options:

```json
{
  "max_skewness": <float>,
  "min_isolated_component_size": <int>,
  "allowed_intersection_types": [<IntersectionType>],
  "min_words_with_many_intersections": {
    "intersections_bound": <int>,
    "qty_bound": <int>
  },
  "forbidden_cells": [ [<x>, <y>], ... ],
  "required_placements": [ { "word": <int>, "horizontal": <bool>, "x": <int>, "y": <int> }, ... ],
  "forbidden_placements": [ { "word": <int>, "horizontal": <bool>, "x": <int>, "y": <int> }, ... ],
  "required_crossings": [ [<word1_index>, <word2_index>], ... ],
  "forbidden_crossings": [ [<word1_index>, <word2_index>], ... ]
}
```

**Options:**

* `max_skewness`: Maximum allowed skewness of the grid (ratio of width to height).
* `min_isolated_component_size`: Minimum size of an isolated component (group of unconnected words).
* `allowed_intersection_types`: List of allowed intersection types. Options are:
    * `CROSSING`: Standard crossing intersection.
    * `HORIZONTAL_OVERLAP`: Horizontal overlap between words.
    * `VERTICAL_OVERLAP`: Vertical overlap between words.
* `min_words_with_many_intersections`: Minimum number of words that must have at least a certain number of intersections.
    * `intersections_bound`: Minimum number of intersections per word.
    * `qty_bound`: Minimum number of words that must have at least `intersections_bound` intersections.
* `forbidden_cells`: List of cells that cannot be used for word placement.
* `required_placements`: List of word placements that must be included in the solution. Each placement is specified as a dictionary with keys `word` (index of the word in the input list), `horizontal` (True for horizontal, False for vertical), `x` (column index), and `y` (row index).
* `forbidden_placements`: List of word placements that must be excluded from the solution.
* `required_crossings`: List of pairs of word indices that must have a crossing intersection.
* `forbidden_crossings`: List of pairs of word indices that must not have a crossing intersection.

### Output Format

The output is a JSON file containing a list of word placements. Each placement is specified as a dictionary with keys `word` (index of the word in the input list), `horizontal` (True for horizontal, False for vertical), `x` (column index), and `y` (row index).


## Example of usage
### Run in command line 
```bash
python crossword_generator.py --input ./example_input.json --x_bound 11 --y_bound 9 --output output.json
```

### Example console output:
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

**The resulting contents of `output.json`:**
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