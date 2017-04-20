# Formalization of type theories and translation

We formalized everything in Coq 8.6.

## Sanity

The purpose here is to state and prove theorems about the sanity of different type theories.

### Theories
* `syntax.v`: Syntax of our type theories with type annotations,
* `ett.v`: Typing rules of ETT (Extensional Type Theory) using syntax from `syntax.v`,
* `ptt.v`: Typing rules of PTT (Paranoid Type Theory) using the same
  syntax, it has more premises to make sure everything is sane.

### Alternative syntax
* `altsyntax.v`: Syntax of type theory with named variables,
* `syntaxes.v`: Translation from `altsyntax` to `syntax`.

### Admissibility in PTT
* `ptt_tactics.v`: Tactics designed to prove judgements in PTT,
* `ptt_admissible.v`: Admissible rules in PTT that are useful in the proof of sanity (*might be temporary?*),
* `ptt_inversion.v`: Inversion lemmata for PTT.

### Sanity Theorem
* `ptt_sanity.v`: Sanity theorem for PTT,
* `ett2ptt.v`: Translation from ETT to PTT, this is a sanity result as it means that we can elaborate the missing premises,
* `ptt2ett.v`: Translation from PTT to ETT,
* `ett_sanity.v`: Sanity theorems for ETT as corollary of the translations and sanity of PTT.

### Useful Results
* `tactics.v`: Some useful tactics to handle sanity and translation PTT ↔ ETT,
* `inversion.v`: Inversion lemmata.

### Uniqueness of Typing
* `uniqueness.v`: Proof of uniqueness of typing for ETT/PTT.

### Elimination of Substitutions (*WIP*)
* `substitution_elim.v`: Proof that substitutions can be eliminated (*WIP*).

## Translations

We offer an alternative translation of the negation of funext
translation from Boulier et al. in the file `negfunext.v` as a proof
of concept.

## LaTeX Generation

* `coq2latex.py`: a script meant to extract the rules from `ett.v` and `ptt.v` to build TeX files that list these rules in *readable* format,
* `mathpartir.sty`: a LaTeX package used for typesetting the rules,
* `rules.tex`: LaTeX file that includes the result of the python script so that you can get one PDF with both PTT and ETT.
