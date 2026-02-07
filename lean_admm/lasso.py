import numpy as np
import matplotlib.pyplot as plt


def soft(u, k):
    return np.sign(u) * np.maximum(np.abs(u) - k, 0.0)


def tau(k, c=1.0, p=1.2):  # p>1 ensures summable
    return c / ((k + 1) ** p)


def update_rho(rho, k, r_norm, s_norm, mu=3.0, c=1.0, p=1.2, eps=1e-12):
    t = tau(k, c, p);
    fac = 0.9 + t
    # Use eps only to avoid division by 0; comparisons still meaningful
    if r_norm > mu * max(s_norm, eps): return rho * fac, t, "mul"
    if s_norm > mu * max(r_norm, eps): return rho / fac, t, "div"
    return rho, t, "keep"


def admm_lasso_adaptive(A, b, lam, rho0=1.0, iters=2000, abstol=1e-4, reltol=1e-3,
                        mu=3.0, c=1.0, p=1.2, verbose=True):
    m, d = A.shape
    x = np.zeros(d);
    z = np.zeros(d);
    y = np.zeros(d);
    rho = float(rho0)
    AtA = A.T @ A;
    Atb = A.T @ b;
    I = np.eye(d)

    r_hist, s_hist, rho_hist, mode_hist = [], [], [], []
    cnt = {"mul": 0, "div": 0, "keep": 0}

    for k in range(iters):
        x = np.linalg.solve(AtA + rho * I, Atb + rho * z - y)
        z_old = z.copy()
        z = soft(x + y / rho, lam / rho)

        r = x - z
        s = rho * (z - z_old)
        y = y + rho * r

        r_norm = float(np.linalg.norm(r))
        s_norm = float(np.linalg.norm(s))
        r_hist.append(r_norm);
        s_hist.append(s_norm);
        rho_hist.append(rho)

        # stopping (Boyd)
        eps_pri = np.sqrt(d) * abstol + reltol * max(np.linalg.norm(x), np.linalg.norm(z))
        eps_dual = np.sqrt(d) * abstol + reltol * (np.linalg.norm(y) / rho)
        if r_norm <= eps_pri and s_norm <= eps_dual:
            break

        rho, t, mode = update_rho(rho, k, r_norm, s_norm, mu=mu, c=c, p=p)
        cnt[mode] += 1
        mode_hist.append(mode)

        if verbose and k % 50 == 0:
            print(f"k={k:4d} r={r_norm:.2e} s={s_norm:.2e} rho={rho_hist[-1]:.2e} -> {rho:.2e} ({mode}, tau={t:.2e})")

    if verbose:
        print("rho update counts:", cnt)

    return np.array(rho_hist), np.array(r_hist), np.array(s_hist), mode_hist


def demo_and_plot():
    np.random.seed(0)
    m, d = 120, 60
    A = np.random.randn(m, d) / np.sqrt(m)
    x_true = np.zeros(d);
    supp = np.random.choice(d, 8, replace=False);
    x_true[supp] = np.random.randn(8)
    b = A @ x_true + 0.05 * np.random.randn(m)

    rho_hist, r_hist, s_hist, _ = admm_lasso_adaptive(
        A, b, lam=0.15, rho0=0.5, iters=2000,
        mu=3.0, c=1.0, p=1.2, verbose=True
    )

    plt.figure(figsize=(7, 4))
    plt.semilogy(r_hist, label="||r_k||")
    plt.semilogy(s_hist, label="||s_k||")
    plt.grid(True, which="both", ls="--", alpha=0.4)
    plt.legend();
    plt.xlabel("k");
    plt.ylabel("norm (log)")
    plt.title("Residual convergence (Adaptive-ρ ADMM, Strategy3)")
    plt.tight_layout();
    plt.show()

    plt.figure(figsize=(7, 3.5))
    plt.plot(rho_hist)
    plt.grid(True, ls="--", alpha=0.4)
    plt.xlabel("k");
    plt.ylabel("ρ_k")
    plt.title("ρ_k trajectory (should change if updates trigger)")
    plt.tight_layout();
    plt.show()


if __name__ == "__main__":
    demo_and_plot()
