# Deep normalized attention library

DeepLean formalizes *Identifiability of Deep Normalized Attention: Or, Machine
Verified Proofs for Neuroalgebraic Geometry*. James Amarel is the formalization
author and responsible maintainer. The code is licensed under MIT.

[Theorem1.lean](Theorem1.lean) proves the scalar depth-two counterexample for
positive normalized injective Borel normalizers, with a witness discontinuous
at zero. [Theorem2.lean](Theorem2.lean) proves positive-temperature softmax
identifiability and its explicit nonempty open dense coordinate locus.

[Definitions.lean](Definitions.lean) gives the mathematical interface and imports
only Mathlib. [Challenge.lean](../../Challenge.lean) repeats its definitions
explicitly and states the three selected clauses. The interface validator checks
that the two definition blocks agree. [Solution.lean](../../Solution.lean)
proves the corresponding declarations in `DeepLean.Attention`.

[DeepAttentionVirtual.lean](DeepAttentionVirtual.lean) gives log-affine corollaries
and boundary interfaces. [SourceArchitecture.lean](SourceArchitecture.lean)
connects the source architecture to virtual coordinates. These supporting
results are public through [DeepLean.lean](../../DeepLean.lean).

The [dependency map](DEPENDENCY_CLOSURE.md) describes all 24 attention modules.
Build from the repository root using the pinned toolchain and dependencies;
there is no nested Lake project. See the [root README](../../README.md) for
commands and [verification instructions](../../README.md#verify) for generating
local results with checked source and tool identities.
