# Adaptive ADMM strategies

Reusable C1 proofs for increase/decrease/keep policies with nonnegative summable modulation.

```lean
import Optlib.Algorithm.AdaptiveADMM.Strategies
```

## Public interface

| Declaration | Purpose |
| --- | --- |
| `AdaptiveADMM.RhoAction` | Multiply rho by `1 + tau`, divide by it, or keep rho |
| `AdaptiveADMM.CertifiedTau` | A sequence with proofs of nonnegativity and summability |
| `AdaptiveADMM.StrategyPolicy` | A certified modulation sequence and an action at each iteration |
| `Strategy3.converges_from_policy` | Full convergence given the actual ADMM recurrence and problem assumptions |
| `AdaptableStrategy` | An update function proved to have the same three-action form |
| `Strategy3.converges_from_adaptable_strategy` | Convergence through that equivalent update function |

The action may depend on the trajectory. The required recurrence connects the policy to the same `admm.ρₙ` used by the convergence theorem. This interface establishes C1; C2 has a separate theorem in `AdaptiveTheorem_converge_c2.lean`.

The convergence bridges take an explicit `admm_kkt : KKTPoint admm`. `Strategy3 admm` contains only penalty-update properties, and `AdaptableStrategy` describes a scalar update without a problem or KKT-point parameter. Existing examples using `Existance_of_kkt` and the empty `Setting` parameter remain supported through `Compatibility.lean`.

## Modules

| File | Contents |
| --- | --- |
| `StrategyPolicy.lean` | Action and policy definitions |
| `Adaptive_Strategy_Convergence.lean` | Strategy3, C1, and the public convergence theorems |
| `AdaptiveStrategyBase.lean` | Residual ratios and branch selectors |
| `TauTemplates.lean` | P-series, geometric sequences, sums, and bounded modulation |
| `VerificationLib.lean` | Summability and finite-prefix lemmas |
| `ClippedPolicy.lean` | Clipping and effective modulation |

## Clipped policies

Under `0 < lower <= rho <= upper` and `0 <= tau`, `ClippedPolicy.update_bounds` preserves the interval. `effectiveAux_bounds` proves that the actual modulation lies between zero and the nominal modulation. `effectiveAux_summable` transfers summability, and `toStrategyPolicy_updateRho` proves equality along the supplied rho sequence.

`trajectory_bounds` derives the interval bounds from the initial value and recurrence. `delayIncrease` delays only increases and preserves decreases; `delayed_residual_branches` states the corresponding ordered branches and clipping exactly.

These statements concern real arithmetic. A concrete candidate still needs its parameter conditions and recurrence correspondence proved, including any exceptional-input behavior.

For the toolchain, default build, and proof-checking command, see the [project README](../../../../README.md).
