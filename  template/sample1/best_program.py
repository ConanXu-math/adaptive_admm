# initial_program.py
# This file is evolved by AlphaEvolve
# Only update_rho (and helpers) should be modified

import numpy as np

def tau(k, c=1.0, p=1.2):
    """
    递减步长（可求和）
    要求 p > 1
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
    自适应 ADMM 罚参数更新规则（论文风格 + 总变差可和）

    更新形式（residual balancing）：
        rho_{k+1} =
            (1 + tau_k) * rho_k        if ||r|| > mu ||s||
            rho_k / (1 + tau_k)        if ||s|| > mu ||r||
            rho_k                      otherwise

    其中 tau_k 为可求和递减序列，
    从而保证 sum_k |rho_{k+1} - rho_k| < +∞
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
