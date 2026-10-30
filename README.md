# DeepLean

Lean proofs for *Identifiability of Deep Normalized Attention: Or, Machine
Verified Proofs for Neuroalgebraic Geometry*. James Amarel is the formalization
author and responsible maintainer. The code is released under the [MIT license](LICENSE).
Manuscript authorship and third-party LaTeX notices are retained separately.

Read the [paper](docs/manuscript/submission.pdf) and the
[proof library](DeepLean/Attention/README.md).

## Mathematical results

The two manuscript theorems are expressed by three declarations in `DeepLean.Attention`:

| Declaration | Content |
| --- | --- |
| `normalizer_counterexample` | A positive normalized injective Borel normalizer, discontinuous at zero, admits distinct scalar depth-two parameters with equal realizations on every two-token input on a nonempty open dense locus. |
| `softmax_identifiability` | Positive-temperature softmax identifies same-depth virtual parameters when the source final map is nonzero and its proper score prefix is non-skew. |
| `softmax_generic_identifiability` | An explicit nonempty Euclidean open dense coordinate locus lies in the source-regular locus and has complete singleton fibers. |

The terminal source score and competing parameter are unrestricted in the pointwise
theorem. Supporting results include the primitive-to-virtual architecture bridge,
log-affine corollaries, and boundary examples.

## Build

Install Git, elan, uv, a compatible C compiler, Ruby, and ripgrep. From the
repository root, prepare the pinned Lean and Python versions and build:

```sh
elan toolchain install "$(cat lean-toolchain)"
uv python install 3.14.5
PYTHON3="$(uv python find 3.14.5)" lake exe cache get
PYTHON3="$(uv python find 3.14.5)" lake build
```

[lean-toolchain](lean-toolchain) pins Lean; [lake-manifest.json](lake-manifest.json)
pins Mathlib, Nerodia, and transitive dependencies. The default targets are
`DeepLean`, `Challenge`, and `Solution`. Challenge contains complete theorem
statements with deliberate proof placeholders; Solution and its proof dependencies
contain no placeholders.

If the default Mathlib cache service is unavailable, use the official Azure
backend with the same pinned dependencies:

```sh
MATHLIB_CACHE_GET_URL=https://lakecache.blob.core.windows.net/mathlib4-master \
  PYTHON3="$(uv python find 3.14.5)" lake exe cache get
```

## Verify

```sh
python3 scripts/test-attention-interface.py
python3 scripts/check-local-proof.py
```

The complete check builds the project, elaborates Challenge and Solution
separately, compares the source interfaces, validates metadata, audits transitive
axioms, and replays the proofs through Comparator, NanoDa, Lean's checker, and
con-ron. It records commands, source hashes, tool identities, and results in a fresh
`.cache/local-proof/` directory. The pinned Lean distribution must provide
`leanexport`, `leanchecker`, `nanoda_bin`, and `con-ron` as well as Lean and Lake.
To choose another output location, pass `--evidence-dir /absolute/path/new-directory`;
existing destinations are refused. The default evidence directory is ignored by Git.
Inspect `report.json`, `axioms.log`, `comparator.log`, and `con-ron.log` in the
output directory. Require explicit acceptance from each checker as well as
successful exits. The permitted transitive axioms are exactly `propext`,
`Quot.sound`, and `Classical.choice`.

The Comparator invocation disables sandboxing. This is local development
verification; it does not establish confined Linux verification or registry
acceptance. Compilation and independent replay do not establish correspondence
between formal statements and manuscript prose; that requires semantic review.

## Manuscript and provenance

The [manuscript sources](docs/manuscript/README.md) build the 23-page paper,
including nine pages of main text and live theorem listings from
[Solution.lean](Solution.lean).

[formalization.yaml](formalization.yaml) records scope, authorship, tool
contributions, and statement correspondence. Contributor instructions are in
[AGENTS.md](AGENTS.md).

Notice of Copyright Assertion (O5226):

© 2026. Triad National Security, LLC. All rights reserved.
This program was produced under U.S. Government contract 89233218CNA000001 for Los Alamos
National Laboratory (LANL), which is operated by Triad National Security, LLC for the U.S.
Department of Energy/National Nuclear Security Administration. All rights in the program are
reserved by Triad National Security, LLC, and the U.S. Department of Energy/National Nuclear
Security Administration. The Government is granted for itself and others acting on its behalf a
nonexclusive, paid-up, irrevocable worldwide license in this material to reproduce, prepare
derivative works, distribute copies to the public, perform publicly and display publicly, and to permit
others to do so.

Copyright 2026
 
Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
 
The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 
THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
