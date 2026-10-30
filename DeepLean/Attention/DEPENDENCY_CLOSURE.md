# Project-specific dependency closure

The public attention modules and their project-local imports are listed below.
`Definitions` imports only Mathlib. External Lean/Mathlib imports are omitted
from this map.

```text
DeepLean.Attention.Theorem1
  -> DeepLean.Attention.NormalizationClassCounterexample
       -> DeepLean.Attention.GeneralNormalization
  -> DeepLean.Attention.SourceArchitecture -> DeepLean.Attention.Basic

DeepLean.Attention.Theorem2 -> DeepLean.Attention.GeneralNormalization

DeepLean.Attention.DeepAttentionVirtual
  -> DeepLean.Attention.Counterexamples -> DeepLean.Attention.Basic
  -> DeepLean.Attention.GeneralNormalization
  -> DeepLean.Attention.Genericity
  -> DeepLean.Attention.NormalizationClassCounterexample

DeepLean.Attention.GeneralNormalization -> DeepLean.Attention.Genericity
DeepLean.Attention.Genericity -> DeepLean.Attention.ArbitraryTokens
DeepLean.Attention.ArbitraryTokens -> DeepLean.Attention.WeightedHierarchy
DeepLean.Attention.WeightedHierarchy -> DeepLean.Attention.Multiplicity
DeepLean.Attention.Multiplicity -> DeepLean.Attention.DeepIdentifiability
DeepLean.Attention.DeepIdentifiability
  -> DeepLean.Attention.DeepHierarchy -> DeepLean.Attention.Hierarchy
       -> DeepLean.Attention.DeepFirstScore -> DeepLean.Attention.ThreeToken
            -> DeepLean.Attention.TwoLayer
                 -> DeepLean.Attention.JetRecovery -> DeepLean.Attention.Basic
                 -> DeepLean.Attention.TwoToken -> DeepLean.Attention.Basic
  -> DeepLean.Attention.MultiAvoidance -> DeepLean.Attention.JetRecovery

DeepLean.Attention.Basic -> DeepLean.Attention.Neuroalgebraic.Attention -> DeepLean.Attention.Neuroalgebraic.Basic
```

## Necessity of every Lean source

| File | Manuscript-facing reason for inclusion |
|---|---|
| `Theorem1.lean` | Exact public wrapper for manuscript Theorem 1. |
| `Theorem2.lean` | Exact public wrappers for both clauses of manuscript Theorem 2 and axiom checks for its two proof lemmas. |
| `DeepAttentionVirtual.lean` | Supporting log-affine and boundary interfaces for the formal-verification appendix. |
| `Neuroalgebraic/Basic.lean` | Matrix and analysis infrastructure used by all attention endpoints. |
| `Neuroalgebraic/Attention.lean` | Column-token normalized attention, virtual weights, and Equation (8)/(15) definitions. |
| `Basic.lean` | Canonical normalized layers and depth-two virtual realization used by both theorems and the boundary example. |
| `JetRecovery.lean` | Secant/limit infrastructure in the Theorem 2 layer-peeling proof. |
| `TwoToken.lean` | Two-token exact dynamics used by the finite-depth hierarchy underlying Theorem 2. |
| `TwoLayer.lean` | Two-layer recovery step used by the Theorem 2 hierarchy. |
| `ThreeToken.lean` | Intermediate arbitrary-token recovery infrastructure imported by the Theorem 2 proof chain. |
| `DeepFirstScore.lean` | `DeepWeights`, `realizeDeep`, and arbitrary-depth first-score recovery used by both theorems. |
| `Hierarchy.lean` | Exact scalar hierarchy used by Theorem 2. |
| `DeepHierarchy.lean` | Finite-depth suffix hierarchy used by Theorem 2. |
| `MultiAvoidance.lean` | Polynomial direction avoidance and dense-direction recovery in Theorem 2. |
| `DeepIdentifiability.lean` | Arbitrary-depth score-list recovery definitions used by Theorem 2. |
| `Multiplicity.lean` | One-distinguished-versus-repeated-token dynamics used by Theorem 2. |
| `WeightedHierarchy.lean` | Formal counterparts of the quadratic/cubic and unequal-suffix manuscript lemmas. |
| `ArbitraryTokens.lean` | Final arbitrary-token, proper-prefix exponential identifiability theorem. |
| `Genericity.lean` | Fixed-depth virtual parameters and the nonempty/open/dense coordinate locus used by both theorem wrappers. |
| `GeneralNormalization.lean` | Positive-temperature reduction and the final Theorem 2 endpoint; also supplies score scaling used in Theorem 1. |
| `Counterexamples.lean` | Kernel-checked full-rank skew example in the boundary-cases subsection (`app:boundaries`). |
| `NormalizationClassCounterexample.lean` | Complete constructive proof underlying Theorem 1. |
| `SourceArchitecture.lean` | Formal Equation (8) bridge from the source architecture to virtual coordinates. |

There are 24 attention modules, including the shared `Definitions` interface.
`DeepLean.Attention.Neuroalgebraic.Attention` imports
`DeepLean.Attention.Definitions`, and the remaining proof chain inherits it.
`Challenge.lean` repeats these definitions and imports only Mathlib;
`Solution.lean` imports the public `DeepLean` root.
