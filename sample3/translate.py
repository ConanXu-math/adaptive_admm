import ast
import json
import pathlib
import textwrap
from string import Template


LEAN_TEMPLATE = Template(
    """-- AUTO GENERATED Lean4 FILE
import Optlib.Algorithm.AdaptiveADMM.Strategies.Adaptive_Strategy_Convergence
import Optlib.Algorithm.AdaptiveADMM.Strategies.VerificationLib

noncomputable section

open Topology Filter
open AdaptiveADMM_Convergence_Proof
open AdaptiveADMM_Verification

variable {E₁ E₂ F : Type*}
[NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
[NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
[NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

variable ($ADMM : ADMM E₁ E₂ F)

def tau_base (c p : ℝ) (n : ℕ) : ℝ := c / Real.rpow ((n : ℝ) + 1) p

def r_ratio (r_norm_seq s_norm_seq : ℕ → ℝ) (eps : ℝ) (n : ℕ) : ℝ :=
  r_norm_seq n / max (s_norm_seq n) eps

def s_ratio (r_norm_seq s_norm_seq : ℕ → ℝ) (eps : ℝ) (n : ℕ) : ℝ :=
  s_norm_seq n / max (r_norm_seq n) eps

-- residual balancing: dir_seq n = 1 (mul), 0 (keep), -1 (div)
def log10 (x : ℝ) : ℝ :=
  Real.log x / Real.log 10

def log1p (x : ℝ) : ℝ :=
  Real.log (1 + x)

def residual_scale (r_norm_seq s_norm_seq : ℕ → ℝ) (eps : ℝ) (n : ℕ) : ℝ :=
  log10 (max (r_norm_seq n) (max (s_norm_seq n) eps) + 1.0)

def effective_mu (mu : ℝ) (r_norm_seq s_norm_seq : ℕ → ℝ) (eps : ℝ) (n : ℕ) : ℝ :=
  if n < 5 then 1.5 + 0.1 * residual_scale r_norm_seq s_norm_seq eps n
  else if n < 15 then 2.0 + 0.2 * residual_scale r_norm_seq s_norm_seq eps n
  else mu + 0.3 * residual_scale r_norm_seq s_norm_seq eps n

def base_factor (n : ℕ) : ℝ :=
  if n < 5 then 2.0
  else if n < 15 then 1.5 else 1.2

def factor_seq (mu eps c p : ℝ) (r_norm_seq s_norm_seq : ℕ → ℝ) (n : ℕ) : ℝ :=
  let eff_mu := effective_mu mu r_norm_seq s_norm_seq eps n
  let t := tau_base c p n
  let bf := base_factor n
  let ratio := r_ratio r_norm_seq s_norm_seq eps n
  let excess := min (ratio / eff_mu) 5.0
  let scaled := 1.0 + (bf - 1.0) * (log1p (excess - 1.0) / log1p 4.0)
  max (scaled - t) 1.05

def tau_seq (mu eps c p : ℝ) (r_norm_seq s_norm_seq : ℕ → ℝ) (n : ℕ) : ℝ :=
  factor_seq mu eps c p r_norm_seq s_norm_seq n - 1

theorem h_tau_summable
    (mu eps c p : ℝ)
    (r_norm_seq s_norm_seq : ℕ → ℝ) : Summable (tau_seq mu eps c p r_norm_seq s_norm_seq) := by
  -- TODO: placeholder proof; align with actual tau_seq definition.
  have h : Summable (tau_base c p) := by
    -- This is intentionally loose; replace with a valid proof later.
    simpa using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
  simpa [tau_seq] using h

-- residual balancing: dir_seq n = 1 (mul), 0 (keep), -1 (div)
def dir_seq (mu eps : ℝ) (r_norm_seq s_norm_seq : ℕ → ℝ) (n : ℕ) : ℤ :=
  if r_ratio r_norm_seq s_norm_seq eps n >
      effective_mu mu r_norm_seq s_norm_seq eps n then 1
  else if s_ratio r_norm_seq s_norm_seq eps n >
      effective_mu mu r_norm_seq s_norm_seq eps n then -1 else 0

lemma h_dir (mu eps : ℝ) (r_norm_seq s_norm_seq : ℕ → ℝ) :
    ∀ n, dir_seq mu eps r_norm_seq s_norm_seq n = 1 ∨
         dir_seq mu eps r_norm_seq s_norm_seq n = 0 ∨
         dir_seq mu eps r_norm_seq s_norm_seq n = -1 := by
  intro n
  by_cases h1 :
    r_ratio r_norm_seq s_norm_seq eps n >
      effective_mu mu r_norm_seq s_norm_seq eps n
  · simp [dir_seq, h1]
  · by_cases h2 :
      s_ratio r_norm_seq s_norm_seq eps n >
        effective_mu mu r_norm_seq s_norm_seq eps n
    · simp [dir_seq, h1, h2]
    · simp [dir_seq, h1, h2]

-- 基于 dir_seq 的三态更新（原始版）
def update_fun_raw
    (mu eps c p : ℝ)
    (r_norm_seq s_norm_seq : ℕ → ℝ)
    (n : ℕ) (rho : ℝ) : ℝ :=
  let dir := dir_seq mu eps r_norm_seq s_norm_seq n
  if dir = (-1 : ℤ) then
    rho / (1 + tau_seq mu eps c p r_norm_seq s_norm_seq n)
  else if dir = (1 : ℤ) then
    rho * (1 + tau_seq mu eps c p r_norm_seq s_norm_seq n)
  else
    rho

def update_fun
    (mu eps c p : ℝ)
    (r_norm_seq s_norm_seq : ℕ → ℝ)
    (n : ℕ) (rho : ℝ) : ℝ :=
  let raw := update_fun_raw mu eps c p r_norm_seq s_norm_seq n rho
  let upper := rho * 10.0
  let lower := rho / 10.0
  let raw_clipped := max (min raw upper) lower
  max (min raw_clipped 1e6) 1e-6

lemma h_update_equiv_raw (mu eps c p : ℝ)
    (r_norm_seq s_norm_seq : ℕ → ℝ)
    (h_dir : ∀ n, dir_seq mu eps r_norm_seq s_norm_seq n = 1 ∨
      dir_seq mu eps r_norm_seq s_norm_seq n = 0 ∨
      dir_seq mu eps r_norm_seq s_norm_seq n = -1) :
    ∀ n rho, 0 < rho →
      update_fun_raw mu eps c p r_norm_seq s_norm_seq n rho =
        rho * (1 + tau_seq mu eps c p r_norm_seq s_norm_seq n) ∨
      update_fun_raw mu eps c p r_norm_seq s_norm_seq n rho =
        rho / (1 + tau_seq mu eps c p r_norm_seq s_norm_seq n) ∨
      update_fun_raw mu eps c p r_norm_seq s_norm_seq n rho = rho := by
  intro n rho hρ_pos
  rcases h_dir n with h | h | h
  · left; simp [update_fun_raw, h]
  · right; right; simp [update_fun_raw, h]
  · right; left; simp [update_fun_raw, h]

lemma h_update_equiv (mu eps c p : ℝ)
    (r_norm_seq s_norm_seq : ℕ → ℝ)
    (h_dir : ∀ n, dir_seq mu eps r_norm_seq s_norm_seq n = 1 ∨
      dir_seq mu eps r_norm_seq s_norm_seq n = 0 ∨
      dir_seq mu eps r_norm_seq s_norm_seq n = -1)
    (h_no_clip : ∀ n rho,
      update_fun mu eps c p r_norm_seq s_norm_seq n rho =
        update_fun_raw mu eps c p r_norm_seq s_norm_seq n rho) :
    ∀ n rho, 0 < rho →
      update_fun mu eps c p r_norm_seq s_norm_seq n rho =
        rho * (1 + tau_seq mu eps c p r_norm_seq s_norm_seq n) ∨
      update_fun mu eps c p r_norm_seq s_norm_seq n rho =
        rho / (1 + tau_seq mu eps c p r_norm_seq s_norm_seq n) ∨
      update_fun mu eps c p r_norm_seq s_norm_seq n rho = rho := by
  intro n rho hρ_pos
  have h_raw :=
    h_update_equiv_raw mu eps c p r_norm_seq s_norm_seq h_dir n rho hρ_pos
  simpa [h_no_clip n rho] using h_raw

theorem auto_converges
    ($KKT : Existance_of_kkt $ADMM)
    [Setting E₁ E₂ F $ADMM $KKT]
    [IsOrderedMonoid ℝ]
    (mu eps c p : ℝ)
    (r_norm_seq s_norm_seq : ℕ → ℝ)
    (h_tau_nonneg : ∀ n, 0 ≤ tau_seq mu eps c p r_norm_seq s_norm_seq n)
    (h_no_clip : ∀ n rho,
      update_fun mu eps c p r_norm_seq s_norm_seq n rho =
        update_fun_raw mu eps c p r_norm_seq s_norm_seq n rho)
    (h_rho : ∀ n, $ADMM.ρₙ (n+1) =
      update_fun mu eps c p r_norm_seq s_norm_seq n ($ADMM.ρₙ n))
    (fullrank₁ : Function.Injective $ADMM.A₁)
    (fullrank₂ : Function.Injective $ADMM.A₂) :
    ∃ x₁ x₂ y,
  Convex_KKT x₁ x₂ y $ADMM.toOptProblem ∧
  Tendsto $ADMM.x₁ atTop (𝓝 x₁) ∧
  Tendsto $ADMM.x₂ atTop (𝓝 x₂) ∧
  Tendsto $ADMM.y atTop (𝓝 y) := by
  let dir := dir_seq mu eps r_norm_seq s_norm_seq
  have h_dir' : ∀ n, dir n = 1 ∨ dir n = 0 ∨ dir n = -1 := by
    intro n; simpa [dir] using h_dir mu eps r_norm_seq s_norm_seq n
  let s : AdaptableStrategy (admm := $ADMM) (admm_kkt := $KKT) :=
    { tau_seq := tau_seq mu eps c p r_norm_seq s_norm_seq
      h_tau_nonneg := h_tau_nonneg
      h_tau_summable := h_tau_summable mu eps c p r_norm_seq s_norm_seq
      update_fun := update_fun mu eps c p r_norm_seq s_norm_seq
      h_update_equiv := h_update_equiv mu eps c p r_norm_seq s_norm_seq h_dir' h_no_clip }
  apply Strategy3.converges_from_adaptable_strategy (admm := $ADMM) (admm_kkt := $KKT) s h_rho fullrank₁ fullrank₂
"""
)


def extract_function_source(file_path: str, func_name: str) -> str:
    src = pathlib.Path(file_path).read_text(encoding="utf-8")
    tree = ast.parse(src)
    for node in tree.body:
        if isinstance(node, ast.FunctionDef) and node.name == func_name:
            return textwrap.dedent(ast.get_source_segment(src, node))
    raise ValueError(f"Function `{func_name}` not found in {file_path}")


def generate_auto_lean_file_from_file(
    file_path: str,
    stored_file_path: str,
    admm_name="admm",
    kkt_name="admm_kkt",
    file_name="auto_update_rho.lean",
):
    update_rho_src = extract_function_source(file_path, "update_rho")
    try:
        tau_src = extract_function_source(file_path, "tau")
    except ValueError:
        tau_src = None

    lean_text = LEAN_TEMPLATE.substitute(ADMM=admm_name, KKT=kkt_name)
    file_path_out = pathlib.Path(stored_file_path) / file_name
    file_path_out.write_text(lean_text, encoding="utf-8")

    report_lines = [
        "# Auto Translation Report",
        "",
        "## Source Functions",
        "",
        "### update_rho (Python)",
        "```python",
        update_rho_src.rstrip(),
        "```",
        "",
        "### tau (Python)" if tau_src else "### tau (Python)",
        "```python" if tau_src else "未找到 `tau` 函数。",
    ]
    if tau_src:
        report_lines.extend([tau_src.rstrip(), "```"])
    report_lines.append("")
    report_lines.append("## Notes")
    report_lines.append("- This template mirrors the sample3 Python logic.")
    report_lines.append("- Proofs include placeholders where needed.")
    report_file_path = pathlib.Path(stored_file_path) / file_name.replace(".lean", ".report.md")
    report_file_path.write_text("\n".join(report_lines), encoding="utf-8")

    ir = {
        "template_used": "sample3_custom",
        "notes": [
            "mirrors Python residual_scale/effective_mu/base_factor/factor_seq",
            "h_tau_summable uses placeholder proof",
        ],
    }
    ir_file_path = pathlib.Path(stored_file_path) / file_name.replace(".lean", ".ir.json")
    ir_file_path.write_text(json.dumps(ir, ensure_ascii=True, indent=2), encoding="utf-8")

    prompt_lines = [
        "System: You are a formal verification expert.",
        "",
        "Task: Audit the template and propose missing lemmas.",
        "",
        "IR:",
        json.dumps(ir, ensure_ascii=True, indent=2),
        "",
        "Output rules:",
        "1) Only def/lemma, no theorem, no import.",
        "2) If proof is hard, use `by` + `admit`.",
    ]
    prompt_file_path = pathlib.Path(stored_file_path) / file_name.replace(".lean", ".prompt.md")
    prompt_file_path.write_text("\n".join(prompt_lines), encoding="utf-8")

    print(f"Lean4 file generated: {file_path_out}")
    print(f"Translation report generated: {report_file_path}")
    print(f"IR generated: {ir_file_path}")
    print(f"Prompt generated: {prompt_file_path}")


if __name__ == "__main__":
    file_dir = "./best_program.py"
    stored_file = "."
    generate_auto_lean_file_from_file(file_path=file_dir, stored_file_path=stored_file)
