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

    # 可求和递减步长
    t = tau(k, c, p)

    # 残差比（仅用于判断方向）
    r_ratio = r_norm / max(s_norm, eps)
    s_ratio = s_norm / max(r_norm, eps)

    # 论文式 residual balancing 更新
    if r_ratio > mu:
        new_rho = rho * (1.0 + t)
        mode = "mul"
    elif s_ratio > mu:
        new_rho = rho / (1.0 + t)
        mode = "div"
    else:
        new_rho = rho
        mode = "keep"

    # 数值稳定性：限制 rho 取值范围
    new_rho = max(min(new_rho, 1e6), 1e-6)

    # 辅助量（用于日志）
    aux = max(r_ratio, s_ratio)

    return new_rho, aux, mode
