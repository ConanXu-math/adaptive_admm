import Lake
open Lake DSL

package optlib where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]

@[default_target]
lean_lib Optlib where
  srcDir := "."
  roots := #[`Optlib]
  globs := #[
    .andSubmodules `Optlib.Algorithm.AdaptiveADMM,
    `Optlib.Convex.BanachSubgradient,
    `Optlib.Convex.ConvexFunction,
    `Optlib.Convex.FiniteDimensionalConvexFunctionsLocallyLipschitz,
    `Optlib.Convex.ImageSubgradientClosed,
    `Optlib.Convex.StronglyConvex,
    `Optlib.Convex.Subgradient,
    `Optlib.Differential.Calculation,
    `Optlib.Differential.Lemmas,
    `Optlib.Function.L1Space,
    `Optlib.Function.Lsmooth,
    `Optlib.Function.MinimaClosedFunction,
    `Optlib.Function.Proximal,
    `Optlib.Optimality.OptimalityConditionOfUnconstrainedProblem]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.24.0-rc1"
