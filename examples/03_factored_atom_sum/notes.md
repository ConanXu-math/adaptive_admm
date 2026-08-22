# Factored Atom Sum

## Scheme idea

This candidate writes the tau schedule in a factored mathematical form. It is
natural for research code, but it must be expanded before proof rendering.

## Proof pattern

The contract distributes the outer fixed coefficient over the sum and emits a
finite atom sum with coefficients `c * 0.8` and `c * 0.2`. The renderer
parenthesizes these composite coefficients in Lean before applying
`h_tau_summable_shifted`.

This example teaches the agent that a numerically convenient expression can be
kept in the candidate while the proof layer canonicalizes it into Optlib atoms.
