# Attention manuscript

[submission.pdf](submission.pdf) is the final 23-page manuscript: main text 1-9,
references 10-11, and appendices 12-23. Its SHA256 is
`3077b598b90d2361deae121abae47ba34f1802e9ea74b9442b660fdaf2db74ee`.
[submission.tex](submission.tex) reads the three theorem declarations directly
from [Solution.lean](../../Solution.lean).

## Authorship and contributions

James Amarel is the formalizer and maintainer. The public code is released under
MIT; manuscript authors and third-party class/style notices remain in the supplied
sources. Codex contributed proof search, debugging, formal-code inspection,
statement interfaces, repository organization, and manuscript editing. The authors
report extensive GPT-5.6 Sol use, primarily at very-high reasoning effort, with
aggregate inference on the order of tens of millions of tokens. This estimate is
distinct from the resource use of reproducible checks. The authors retain
responsibility for the mathematical claims and exposition.

## Formal correspondence

| Manuscript clause | Declaration in `DeepLean.Attention` |
| --- | --- |
| Theorem 1 | `normalizer_counterexample` |
| Theorem 2, pointwise identifiability | `softmax_identifiability` |
| Theorem 2, generic locus and complete fibers | `softmax_generic_identifiability` |

[comparator.json](../../comparator.json) selects all three declarations.
[Challenge.lean](../../Challenge.lean) imports only Mathlib and mirrors the
[definition interface](../../DeepLean/Attention/Definitions.lean).
Run `python3 scripts/check-local-proof.py` from the repository root for the complete
local check. Its scope and generated evidence are described in the
[verification instructions](../../README.md#verify).

## Build

Use PDFLaTeX, BibTeX, `latexmk`, and the packages requested by the source, including
`algorithm2e`. From this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error submission.tex
```

The source uses the supplied [jmlr class](jmlr.cls) and
[jmlrutils package](jmlrutils.sty), version 1.30 (2022-02-09).
Author information and proceedings metadata are preserved.
[latexmkrc](latexmkrc) normalizes bibliography page ranges to ordinary hyphens.
The listings require the relative path `../../Solution.lean`; no private checkout
or agent configuration is required. Compiler intermediates remain ignored; the
published PDF is retained explicitly.

## Third-party notices

The unmodified JMLR class and package are by Nicola L. C. Talbot.
Copyright 2006-2022 Nicola Talbot. This material is subject to the
[LaTeX Project Public License](https://www.latex-project.org/lppl/lppl-1-3c/),
version 1.3 or later. The files retain their original copyright and license
headers. The complete, unmodified JMLR 1.30 distribution, including its sources,
is available from [CTAN](https://ctan.org/pkg/jmlr).
