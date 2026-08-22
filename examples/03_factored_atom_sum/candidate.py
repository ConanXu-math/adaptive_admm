def tau(k, c=1.0, p=1.2):
    n = k + 1.0
    return c * (0.8 / (n ** p) + 0.2 / (n ** (p + 0.5)))


def update_rho(rho, k, r_norm, s_norm, mu=3.0, c=1.0, p=1.2, eps=1e-12):
    t = tau(k, c, p)
    if r_norm > mu * max(s_norm, eps):
        new_rho = rho * (1.0 + t)
        mode = "mul"
    elif s_norm > mu * max(r_norm, eps):
        new_rho = rho / (1.0 + t)
        mode = "div"
    else:
        new_rho = rho
        mode = "keep"
    return new_rho, t, mode
