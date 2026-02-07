# initial_program.py
# This file is evolved by AlphaEvolve
# Only update_rho (and helpers) should be modified

import numpy as np


def tau(k, c=1.0, p=1.2):
    """
    Diminishing step size sequence.

    Requirements:
    - tau_k >= 0
    - summable for p > 1
    - depends only on k and fixed constants
    """
    return c / ((k + 1.0) ** p)


def update_rho(
    rho,
    k,
    r_norm,
    s_norm,
    mu=3.0,
    c=1.0,
    p=1.2,
    eps=1e-12,
):
    """
    C1-safe adaptive ADMM penalty update rule.

    Conservative by design.
    """

    # Summable step size (independent of residuals)
    t = tau(k, c, p)

    # Direction logic ONLY (may depend on residuals)
    if r_norm > mu * max(s_norm, eps):
        new_rho = rho * (1.0 + t)
        mode = "mul"

    elif s_norm > mu * max(r_norm, eps):
        new_rho = rho / (1.0 + t)
        mode = "div"

    else:
        new_rho = rho
        mode = "keep"

    # Auxiliary scalar: purely tau_k (no residual dependence)
    aux = t

    return new_rho, aux, mode
