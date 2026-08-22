# Standard P-Series Sum2

## Scheme idea

This is the smallest multi-term tau schedule. The candidate uses two p-series
decay atoms and preserves the Strategy3 rho update shape exactly.

## Proof pattern

The contract recognizes `tau` as `pseries_sum2`. The Lean certificate uses
`tau_seq_sum2` and `h_tau_summable_sum2` from `TauTemplates.lean`, then wraps the
three-state update as a typed `StrategyPolicy` and applies
`Strategy3.converges_from_policy`.

The update signature intentionally uses tau-specific parameters instead of
requiring literal `c,p`. This teaches the agent that parameter names may follow
the scheme, while the rho/update/evaluator interface stays fixed.
