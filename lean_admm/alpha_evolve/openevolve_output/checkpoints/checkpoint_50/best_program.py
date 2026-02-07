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
    # Compute imbalance ratio (always >= 1)
    if r_norm > eps and s_norm > eps:
        ratio = max(r_norm / s_norm, s_norm / r_norm)
    else:
        ratio = 1.0
    
    # Adjust step size based on ratio, but keep it bounded
    # Use a moderate scaling: min(ratio / mu, 1.4) to prevent excessive updates
    scale = min(ratio / mu, 1.4)
    adjusted_t = t * (1.0 + 0.4 * scale)  # Increase t by up to 56% when ratio is large
    
    if r_norm > mu * max(s_norm, eps):
        factor = 1.0 + adjusted_t
        new_rho = rho * factor
        mode = "mul"

    elif s_norm > mu * max(r_norm, eps):
        factor = 1.0 + adjusted_t
        new_rho = rho / factor
        mode = "div"

    else:
        new_rho = rho
        mode = "keep"

    # Auxiliary scalar: include information about adjustment (C1-safe as it's based on t)
    aux = adjusted_t

    return new_rho, aux, mode
