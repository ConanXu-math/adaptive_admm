def tau(k, c1=1.0, p1=1.2, c2=0.2, p2=2.0):
    n = k + 1.0
    return c1 / (n ** p1) + c2 / (n ** p2)


def update_rho(rho, k, r_norm, s_norm, mu=3.0, c1=1.0, p1=1.2, eps=1e-12):
    t = tau(k, c1, p1)
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
