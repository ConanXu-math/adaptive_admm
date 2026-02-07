"""
Evaluator for Adaptive-ρ ADMM (LASSO)

This evaluator scores candidate update_rho programs based on:
- convergence speed
- final residual quality
- stability of rho updates

NO gradient or attribution is provided by default.
Only scalar metrics are returned.

Set RICH_FEEDBACK=1 to enable detailed diagnostics
(primal vs dual dominance, rho oscillation hints).
"""

import os
import sys
import time
import traceback
import importlib.util
import numpy as np
from alpha_evolve.translate_LLM import check_results_formulation, read_source_code, get_lean4_results
from pathlib import Path
import uuid
import subprocess

# optlib 项目根目录（lean_admm/alpha_evolve/ -> optlib/）
_OPTLIB_ROOT = Path(__file__).resolve().parent.parent.parent
LEAN_PROJECT_ROOT = _OPTLIB_ROOT
LEAN_DIR = LEAN_PROJECT_ROOT / "Optlib" / "Algorithm" / "AdaptiveADMM" / "Strategies"


def write_unique_lean(code: str) -> Path:
    fname = f"generated_prove_{uuid.uuid4().hex[:8]}.lean"
    path = LEAN_DIR / fname
    path.write_text(code, encoding="utf-8")
    return path


RICH_FEEDBACK = os.environ.get("RICH_FEEDBACK", "0") == "1"


# -----------------------------
# Core ADMM components (fixed)
# -----------------------------

def soft(u, k):
    return np.sign(u) * np.maximum(np.abs(u) - k, 0.0)


def run_admm(update_rho_fn, seed=0, max_iters=2000):
    np.random.seed(seed)

    m, d = 120, 60
    A = np.random.randn(m, d) / np.sqrt(m)

    x_true = np.zeros(d)
    supp = np.random.choice(d, 8, replace=False)
    x_true[supp] = np.random.randn(8)
    b = A @ x_true + 0.05 * np.random.randn(m)

    lam = 0.15
    rho = 0.5

    x = np.zeros(d)
    z = np.zeros(d)
    y = np.zeros(d)

    AtA = A.T @ A
    Atb = A.T @ b
    I = np.eye(d)

    r_hist, s_hist, rho_hist = [], [], []

    for k in range(max_iters):
        x = np.linalg.solve(AtA + rho * I, Atb + rho * z - y)
        z_old = z.copy()
        z = soft(x + y / rho, lam / rho)

        r = x - z
        s = rho * (z - z_old)
        y = y + rho * r

        r_norm = float(np.linalg.norm(r))
        s_norm = float(np.linalg.norm(s))

        r_hist.append(r_norm)
        s_hist.append(s_norm)
        rho_hist.append(rho)

        eps_pri = np.sqrt(d) * 1e-4 + 1e-3 * max(
            np.linalg.norm(x), np.linalg.norm(z)
        )
        eps_dual = np.sqrt(d) * 1e-4 + 1e-3 * (np.linalg.norm(y) / max(rho, 1e-12))

        if r_norm <= eps_pri and s_norm <= eps_dual:
            return {
                "converged": True,
                "iters": k + 1,
                "r_hist": r_hist,
                "s_hist": s_hist,
                "rho_hist": rho_hist,
            }

        rho, _, _ = update_rho_fn(
            rho, k, r_norm, s_norm, mu=3.0, c=1.0, p=1.2
        )

    return {
        "converged": False,
        "iters": max_iters,
        "r_hist": r_hist,
        "s_hist": s_hist,
        "rho_hist": rho_hist,
    }


# -----------------------------
# OpenEvolve evaluator API
# -----------------------------

def evaluate(program_path: str) -> dict:
    start_time = time.time()

    try:
        # Load candidate program
        spec = importlib.util.spec_from_file_location("program", program_path)
        module = importlib.util.module_from_spec(spec)
        sys.modules["program"] = module
        spec.loader.exec_module(module)

        if not hasattr(module, "update_rho"):
            return _error_result("Program must define update_rho()")

        code = read_source_code(program_path)
        issues, is_valid, math_form = check_results_formulation(code)
        if not is_valid:
            eval_time = time.time() - start_time

            return {
                "combined_score": 0.0,  # ← 关键：直接淘汰
                "metrics": {
                    "converged": False,
                    "iters": float("inf"),
                    "combined_score": 0.0,
                    "formal_valid": False,
                },
                "artifacts": {
                    "formal_check": is_valid,
                    "issues": issues,
                    "eval_time": eval_time,
                },
            }

        result = run_admm(module.update_rho)
        eval_time = time.time() - start_time

        lean4_code = get_lean4_results(math_form)

        lean_path = write_unique_lean(lean4_code)

        proc = subprocess.run(
            [
                "lake", "env", "lean",
                str(lean_path.relative_to(LEAN_PROJECT_ROOT)),
            ],
            cwd=LEAN_PROJECT_ROOT,
            capture_output=True,
            text=True,
            timeout=120,
        )

        if proc.returncode != 0:
            formal_valid = "Lean4_Not_Auto_Proven"
            score = 0.5
        else:
            formal_valid = "Lean4_Auto_Proven"
            score = 1

        # -----------------------------
        # Metrics (what evolution sees)
        # -----------------------------
        if not result["converged"]:
            combined_score = 0.0
        else:
            combined_score = score * (
                    1.0 / result["iters"])

        metrics = {
            "converged": result["converged"],
            "iters": result["iters"],
            "combined_score": combined_score,
        }

        artifacts = build_artifacts(result, eval_time)

        return {
            "combined_score": combined_score,  # ← 关键
            "metrics": metrics,
            "artifacts": artifacts,
            "formal_certification": formal_valid
        }


    except Exception as e:
        return _exception_result(e)


# -----------------------------
# Feedback construction
# -----------------------------

def build_artifacts(result, eval_time):
    artifacts = {}

    artifacts["status"] = (
        "CONVERGED" if result["converged"] else "DID NOT CONVERGE"
    )
    artifacts["iterations"] = result["iters"]
    artifacts["eval_time"] = f"{eval_time:.3f}s"

    if RICH_FEEDBACK and result["converged"]:
        r = np.array(result["r_hist"])
        s = np.array(result["s_hist"])
        rho = np.array(result["rho_hist"])

        artifacts["diagnostics"] = {
            "final_r_norm": float(r[-1]),
            "final_s_norm": float(s[-1]),
            "rho_variance": float(np.var(rho)),
            "primal_dual_ratio_final": float(r[-1] / (s[-1] + 1e-12)),
        }

        if np.var(rho) > 1.0:
            artifacts["hint"] = "ρ oscillates heavily; consider smoother updates."
        elif result["iters"] > 800:
            artifacts["hint"] = "Converges slowly; try more aggressive early adaptation."
        else:
            artifacts["hint"] = "Stable convergence."

    return artifacts


# -----------------------------
# Error handling (same pattern)
# -----------------------------

def _error_result(message: str) -> dict:
    return {
        "metrics": {
            "converged": False,
            "iters": 0,
            "combined_score": 0.0,
        },
        "artifacts": {
            "error": message,
            "status": "ERROR",
        },
    }


def _exception_result(e: Exception) -> dict:
    return {
        "metrics": {
            "converged": False,
            "iters": 0,
            "combined_score": 0.0,
        },
        "artifacts": {
            "exception": str(e),
            "traceback": traceback.format_exc(),
            "status": "EXCEPTION",
        },
    }
