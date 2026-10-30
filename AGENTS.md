# Contributor instructions

Read [README.md](README.md) and the relevant source, imports, and neighboring
declarations before editing. Keep repository-local documentation links valid.

Preserve theorem names, statements, mathematical hypotheses, toolchain versions,
and dependency revisions unless the requested task explicitly changes them.
Put reusable proofs under `DeepLean/` and expose public modules through `DeepLean.lean`.
Do not add axioms, unsafe declarations, or proof placeholders to completed proofs.
Only `Challenge.lean` may contain deliberate proof placeholders; its theorem
statements must remain complete and agree with `Solution.lean`.

Keep the selected declarations and permitted axioms in `comparator.json` fixed.
Never weaken statements, disable NanoDa, or bypass checks to obtain acceptance.
Before completing proof or verification-interface changes, run from the root:

```sh
python3 scripts/test-attention-interface.py
python3 scripts/check-local-proof.py
```

Inspect the actual axiom and checker logs. Compilation, independent proof replay,
and correspondence with the manuscript are separate claims. Retain source and
tool identities in the generated local evidence; follow the
[verification instructions](README.md#verify).

Use formal, precise mathematical prose. Preserve established notation, explicit
quantifiers, and logical connections. For manuscript changes, inspect neighboring
arguments, check cited claims against primary sources, build with the documented
command, and inspect affected PDF pages. An audit reports findings unless repairs
are separately requested; prior reviews do not exempt claims from scrutiny.

Keep caches, environments, credentials, and generated intermediates ignored.
The published manuscript PDF is an explicit exception. Keep generated verification
logs under the ignored `.cache/local-proof/` directory.
Preserve the MIT license, the complete copyright footer at the bottom of README.md,
manuscript author information, and third-party notices. Do not commit or publish
without authorization.
