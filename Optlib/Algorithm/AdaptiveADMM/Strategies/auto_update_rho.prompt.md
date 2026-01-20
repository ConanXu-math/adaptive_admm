System: You are a formal verification expert. Extract the mathematical logic from Python code into JSON for Lean 4.

Task: Convert the IR below into Lean interface fragments (ONLY define tau_seq/dir_seq/update_fun/h_update_equiv/h_tau_summable).
Do NOT write theorems or imports.

IR:
{
  "tau": {
    "type": "standard",
    "subtype": "p_series",
    "params": [
      "c",
      "p"
    ],
    "constraints": [
      {
        "name": "hp",
        "expr": "1 < p"
      }
    ],
    "lean_expr": "c / Real.rpow ((n : \u211d) + 1) p"
  },
  "dir_logic": "if r_norm_seq n / max (s_norm_seq n) eps > mu then 1 else if s_norm_seq n / max (r_norm_seq n) eps > mu then -1 else 0",
  "symbols": {
    "mu": "mu",
    "eps": "eps",
    "r_norm_seq": "r_norm_seq",
    "s_norm_seq": "s_norm_seq",
    "r_ratio": "r_ratio",
    "s_ratio": "s_ratio"
  },
  "proof_obligations": [
    "tau_summable",
    "update_equiv"
  ],
  "notes": [
    "uses r_ratio, s_ratio, eps",
    "residual balancing with mul/div/keep",
    "template_used=residual_balancing"
  ]
}

Output rules:
1) Only def/lemma, no theorem, no import.
2) Do not introduce new assumptions beyond IR symbols.
3) If proof is hard, use `by` + `admit`.