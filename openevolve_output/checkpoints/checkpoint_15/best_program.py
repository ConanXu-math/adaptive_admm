# initial_program.py
# This file is evolved by AlphaEvolve
# Only update_rho (and helpers) should be modified

import numpy as np


def tau(k, c=1.0, p=1.2):
    """
    Diminishing step size, must be summable.
    AlphaEvolve is allowed to change this.
    """
    return c / ((k + 1) ** p)


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
    Adaptive ADMM penalty update rule.

    Inputs:
        rho    : current penalty parameter
        k      : iteration index
        r_norm : ||primal residual||
        s_norm : ||dual residual||
    Outputs:
        new_rho : updated rho
        aux     : any auxiliary scalar (logged but not used)
        mode    : string label ("mul", "div", "keep", etc.)

    AlphaEvolve may change the internal logic,
    but MUST respect the signature and return types.
    """
    # Adjust mu based on iteration to be more aggressive early on
    # For early iterations, use a smaller threshold to update more frequently
    if k < 10:
        effective_mu = 2.0
    else:
        effective_mu = mu
    
    # Compute the ratio of residuals, handling small values
    r_ratio = r_norm / max(s_norm, eps)
    s_ratio = s_norm / max(r_norm, eps)
    
    # Determine update factor based on iteration
    # Early iterations: larger updates, later: smaller updates
    if k < 5:
        base_factor = 1.5
    elif k < 20:
        base_factor = 1.2
    else:
        base_factor = 1.1
    
    # Use tau to add diminishing component
    t = tau(k, c, p)
    # The adjustment factor should be between base_factor and 1/base_factor
    # But we want to make sure updates are not too small
    if r_ratio > effective_mu:
        # Primal residual is too large relative to dual residual
        # Increase rho to penalize primal infeasibility more
        # Use a factor that decreases with iterations
        factor = base_factor - t
        # Ensure factor is at least 1.05
        factor = max(factor, 1.05)
        new_rho = rho * factor
        mode = "mul"
    elif s_ratio > effective_mu:
        # Dual residual is too large relative to primal residual
        # Decrease rho to penalize dual infeasibility more
        factor = base_factor - t
        factor = max(factor, 1.05)
        new_rho = rho / factor
        mode = "div"
    else:
        # Both residuals are balanced
        new_rho = rho
        mode = "keep"
    
    # For numerical stability, bound rho between 1e-6 and 1e6
    new_rho = max(min(new_rho, 1e6), 1e-6)
    
    # Use the ratio as auxiliary information
    aux = r_ratio if r_ratio > s_ratio else s_ratio
    return new_rho, aux, mode
