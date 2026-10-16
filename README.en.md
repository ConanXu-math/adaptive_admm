# Adaptive ADMM in Lean

[简体中文](README.md) | English

A Lean library for convergence of two-block ADMM with a variable scalar penalty. It contains the C1 and C2 convergence proofs and a reusable interface for summable increase/decrease/keep policies.

## Build and import

The project pins Lean and mathlib to `v4.24.0-rc1`. With elan installed, run from this directory:

```bash
lake exe cache get
lake build
```

The default build includes the public entry point, all AdaptiveADMM modules, and their supporting mathematics. Import the library with:

```lean
import Optlib.Algorithm.AdaptiveADMM

#check AdaptiveADMM_Convergence_Proof.adaptive_admm_convergence_c1
#check AdaptiveADMM_Convergence_Proof.adaptive_admm_convergence
#check Strategy3.converges_from_policy
#check KKTPoint
```

The unsuffixed `adaptive_admm_convergence` is the C2 theorem. Existing imports of individual modules remain available. `Optlib.lean` belongs to the broader upstream library; use the AdaptiveADMM entry point above for this project.

To check a proof that imports the library:

```bash
lake env lean -E hasSorry -DautoImplicit=false -DrelaxedAutoImplicit=false MyProof.lean
```

## Mathematical scope

The problem is `min f₁(x₁) + f₂(x₂)` subject to `A₁ x₁ + A₂ x₂ = b`, in finite-dimensional real inner-product spaces. The full convergence theorems assume:

- Convex, everywhere finite real-valued objectives and an existing KKT point.
- Exact minimization of both ADMM subproblems.
- Injective `A₁` and `A₂`.
- A penalty sequence bounded above and bounded away from zero.
- Fixed multiplier relaxation `0 < τ < (1 + sqrt 5) / 2`.
- The relative-penalty variation condition C1 or C2.

`Strategy3.converges_from_policy` derives C1 from a nonnegative summable modulation sequence and the stated three-action recurrence. Clipping uses the effective modulation along the actual penalty sequence. A concrete candidate must establish its parameters, recurrence, and problem assumptions; the generic theorem does not establish Python-to-Lean correspondence.

## Explicit reference points

`KKTPoint admm` stores a primal-dual point and its KKT proof. Errors and energies take that point as an ordinary argument: `e₁ admm reference n`, `ey admm reference n`, and `g1 admm reference n`. `Condition_C1 admm` and `Condition_C2 admm` concern only the penalty sequence.

The convergence proofs pass the original reference to the boundedness and subsequence construction. They then pass the resulting `limitKKT` to the final error and energy estimates, keeping the selected subsequence fixed. Core proofs do not use `Setting` or infer a reference point through typeclass search.

`Compatibility.lean` retains the old `Existance_of_kkt` spelling and empty `Setting` parameter for older proofs. New proofs should use `KKTPoint` and the explicit arguments above.

## Source organization

All paths below are relative to `Optlib/Algorithm/AdaptiveADMM/`.

| Module | Responsibility |
| --- | --- |
| `AdaptiveScheme.lean` | Problem, iteration, KKT relation, and `KKTPoint` |
| `AdaptiveDefinitions.lean` | Errors, energies, and auxiliary sequences with explicit arguments |
| `AdaptiveOptimality.lean` | Subproblem convexity, differentiation, and subgradient membership |
| `AdaptiveEnergyIdentities.lean` | Residual identities and subgradient monotonicity estimates |
| `AdaptiveEnergyDescent.lean` | Cross-term bounds and the common energy decrease inequality |
| `AdaptiveLemmas.lean` | Import entry point for the common optimality and descent results |
| `AdaptiveCondition1.lean`, `AdaptiveCondition2.lean` | Penalty variation, energy bounds, and vanishing residuals |
| `BoundednessC1.lean`, `BoundednessC2.lean` | Product normalization, bounded trajectories, and subsequence selection |
| `ClusterPointC1.lean`, `ClusterPointC2.lean` | Subsequence limits and construction of the KKT cluster point |
| `AdaptiveTheorem_converge_c1.lean`, `AdaptiveTheorem_converge_c2.lean` | Recentered energy and convergence of the full sequence |
| `SequenceConvergence.lean` | Shared scalar argument from a zero subsequence to a zero limit |
| `AdaptiveProductBounds.lean`, `AdaptiveInv_bounded.lean` | Product estimates and bounds for injective linear maps |
| `Strategies.lean`, `Strategies/` | Policies, summable modulation sequences, clipping, and the C1 connection |

The supporting `Optlib/Convex`, `Optlib/Differential`, `Optlib/Function`, and `Optlib/Optimality` modules supply the reused mathematics. See the [strategy guide](Optlib/Algorithm/AdaptiveADMM/Strategies/README.md) for the policy interface.

## License

The project retains the upstream [Apache 2.0 license](LICENSE.txt) and source author notices.
