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
    # Compute the ratio of residuals, handling small values
    r_ratio = r_norm / max(s_norm, eps)
    s_ratio = s_norm / max(r_norm, eps)
    
    # Dynamic threshold based on iteration and residual magnitude
    # Early iterations: be more aggressive with a lower threshold
    # Also, if residuals are large, be more sensitive
    residual_scale = np.log10(max(r_norm, s_norm, eps) + 1.0)
    # Scale mu based on iteration and residual scale
    if k < 5:
        # Very early: very aggressive
        effective_mu = 1.5 + 0.1 * residual_scale
        base_factor = 2.0
    elif k < 15:
        # Early: moderately aggressive
        effective_mu = 2.0 + 0.2 * residual_scale
        base_factor = 1.5
    else:
        # Later: more conservative
        effective_mu = mu + 0.3 * residual_scale
        base_factor = 1.2
    
    # Cap effective_mu to prevent being too sensitive
    effective_mu = min(effective_mu, 10.0)
    
    # Use tau to add diminishing component
    t = tau(k, c, p)
    
    # Determine update based on both ratios
    # Use a smoother approach: compute a weighted decision
    if r_ratio > effective_mu:
        # Primal residual is too large relative to dual residual
        # Make the update factor depend on how large the ratio is
        excess_ratio = min(r_ratio / effective_mu, 5.0)
        # The factor should be between base_factor and 1.0, but we want >1
        # Use a logarithmic scaling
        factor = 1.0 + (base_factor - 1.0) * np.log1p(excess_ratio - 1.0) / np.log1p(4.0)
        # Apply diminishing returns with t
        factor = max(factor - t, 1.05)
        new_rho = rho * factor
        mode = "mul"
    elif s_ratio > effective_mu:
        # Dual residual is too large relative to primal residual
        excess_ratio = min(s_ratio / effective_mu, 5.0)
        factor = 1.0 + (base_factor - 1.0) * np.log1p(excess_ratio - 1.0) / np.log1p(4.0)
        factor = max(factor - t, 1.05)
        new_rho = rho / factor
        mode = "div"
    else:
        # Both residuals are balanced
        new_rho = rho
        mode = "keep"
    
    # For numerical stability, bound rho between 1e-6 and 1e6
    # Also, prevent very large jumps by limiting the change per iteration
    max_change = 10.0
    if new_rho > rho * max_change:
        new_rho = rho * max_change
    elif new_rho < rho / max_change:
        new_rho = rho / max_change
    
    new_rho = max(min(new_rho, 1e6), 1e-6)
    
    # Use a combined measure as auxiliary information
    aux = max(r_ratio, s_ratio)
    return new_rho, aux, mode
