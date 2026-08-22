# Local Atom Sum

## Scheme idea

This candidate names intermediate pieces before returning the tau sum. This is
the style an auto research agent often writes while exploring a scheme.

## Proof pattern

The contract inlines `poly_term` and `geo_term`, then recognizes a finite sum of
summable atoms: one shifted p-series atom and one geometric atom. The Lean
certificate builds the tau function explicitly as a finite atom sum and combines
`h_tau_summable_shifted` with `h_tau_summable_geom`.

This example teaches the agent that readable local variables are allowed when
they expand to Optlib-supported summable atoms.
