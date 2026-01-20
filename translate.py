import ast
import textwrap
import pathlib
import json
from typing import Dict, Any, Callable, List


TEMPLATE_REGISTRY: Dict[str, Callable[[Dict[str, Any], str, str], List[str]]] = {}


def register_template(name: str, render_fn: Callable[[Dict[str, Any], str, str], List[str]]) -> None:
    TEMPLATE_REGISTRY[name] = render_fn


def _render_header(admm_name: str) -> List[str]:
    return [
        "-- AUTO GENERATED Lean4 FILE",
        "import Optlib.Algorithm.AdaptiveADMM.Strategies.Adaptive_Strategy_Convergence",
        "import Optlib.Algorithm.AdaptiveADMM.Strategies.VerificationLib",
        "\nnoncomputable section\n",
        "open Topology Filter",
        "open AdaptiveADMM_Convergence_Proof",
        "open AdaptiveADMM_Verification\n",
        "variable {E₁ E₂ F : Type*}",
        "[NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]",
        "[NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]",
        "[NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]\n",
        f"variable ({admm_name} : ADMM E₁ E₂ F)\n",
    ]


def _render_standard(ir: Dict[str, Any], admm_name: str, kkt_name: str) -> List[str]:
    tau = ir.get("tau", {})
    subtype = tau.get("subtype", "p_series")
    params = tau.get("params", ["c", "p"])
    constraints = tau.get("constraints", [{"name": "hp", "expr": "1 < p"}])
    symbols = ir.get("symbols", {})

    mu_name = symbols.get("mu", "mu")
    eps_name = symbols.get("eps", "eps")
    r_norm_name = symbols.get("r_norm_seq", "r_norm_seq")
    s_norm_name = symbols.get("s_norm_seq", "s_norm_seq")
    r_ratio_name = symbols.get("r_ratio", "r_ratio")
    s_ratio_name = symbols.get("s_ratio", "s_ratio")

    c_name = params[0] if len(params) > 0 else "c"
    p_name = params[1] if len(params) > 1 else "p"
    hp_name = constraints[0]["name"] if constraints else "hp"

    tau_params = " ".join(params) if params else "c p"
    tau_expr = tau.get("lean_expr", "0")

    lines: List[str] = []
    lines.append(f"def tau_seq ({tau_params} : ℝ) (n : ℕ) : ℝ := {tau_expr}")
    lines.append("")
    lines.append(
        f"theorem h_tau_summable ({tau_params} : ℝ) ({hp_name} : 1 < {p_name}) : Summable (tau_seq {c_name} {p_name}) := by"
    )
    if subtype == "geometric":
        lines.append("  -- geometric template")
        lines.append("  exact geometric_summable_template c p (by admit) (by admit)")
    else:
        lines.append(f"  exact p_series_summable_template {c_name} {p_name} {hp_name}")
    lines.append("")
    lines.append(
        f"def {r_ratio_name} ({r_norm_name} {s_norm_name} : ℕ → ℝ) ({eps_name} : ℝ) (n : ℕ) : ℝ :="
    )
    lines.append(f"  {r_norm_name} n / max ({s_norm_name} n) {eps_name}")
    lines.append("")
    lines.append(
        f"def {s_ratio_name} ({r_norm_name} {s_norm_name} : ℕ → ℝ) ({eps_name} : ℝ) (n : ℕ) : ℝ :="
    )
    lines.append(f"  {s_norm_name} n / max ({r_norm_name} n) {eps_name}")
    lines.append("")
    lines.append("-- residual balancing: dir_seq n = 1 (mul), 0 (keep), -1 (div)")
    lines.append(
        f"def dir_seq ({mu_name} {eps_name} : ℝ) ({r_norm_name} {s_norm_name} : ℕ → ℝ) (n : ℕ) : ℤ :="
    )
    lines.append(f"  if {r_ratio_name} {r_norm_name} {s_norm_name} {eps_name} n > {mu_name} then 1")
    lines.append(
        f"  else if {s_ratio_name} {r_norm_name} {s_norm_name} {eps_name} n > {mu_name} then -1 else 0"
    )
    lines.append("")
    lines.append(
        f"lemma h_dir ({mu_name} {eps_name} : ℝ) ({r_norm_name} {s_norm_name} : ℕ → ℝ) :"
    )
    lines.append("    ∀ n, dir_seq mu eps r_norm_seq s_norm_seq n = 1 ∨")
    lines.append("         dir_seq mu eps r_norm_seq s_norm_seq n = 0 ∨")
    lines.append("         dir_seq mu eps r_norm_seq s_norm_seq n = -1 := by")
    lines.append("  intro n")
    lines.append(f"  by_cases h1 : {r_ratio_name} {r_norm_name} {s_norm_name} {eps_name} n > {mu_name}")
    lines.append("  · simp [dir_seq, h1]")
    lines.append(
        f"  · by_cases h2 : {s_ratio_name} {r_norm_name} {s_norm_name} {eps_name} n > {mu_name}"
    )
    lines.append("    · simp [dir_seq, h1, h2]")
    lines.append("    · simp [dir_seq, h1, h2]")
    lines.append("")
    lines.append("-- 基于 dir_seq 的三态更新")
    lines.append("def update_fun (tau : ℕ → ℝ) (dir : ℕ → ℤ) (n : ℕ) (rho : ℝ) : ℝ :=")
    lines.append("  if dir n = (-1 : ℤ) then")
    lines.append("    rho / (1 + tau n)")
    lines.append("  else if dir n = (1 : ℤ) then")
    lines.append("    rho * (1 + tau n)")
    lines.append("  else")
    lines.append("    rho")
    lines.append("")
    lines.append("lemma h_update_equiv (tau : ℕ → ℝ) (dir : ℕ → ℤ)")
    lines.append("    (h_dir : ∀ n, dir n = 1 ∨ dir n = 0 ∨ dir n = -1) :")
    lines.append("    ∀ n rho, 0 < rho →")
    lines.append("      update_fun tau dir n rho = rho * (1 + tau n) ∨")
    lines.append("      update_fun tau dir n rho = rho / (1 + tau n) ∨")
    lines.append("      update_fun tau dir n rho = rho := by")
    lines.append("  intro n rho hρ_pos")
    lines.append("  rcases h_dir n with h | h | h")
    lines.append("  · left; simp [update_fun, h]")
    lines.append("  · right; right; simp [update_fun, h]")
    lines.append("  · right; left; simp [update_fun, h]")
    lines.append("")
    lines.append("theorem auto_converges")
    lines.append(f"    ({kkt_name} : Existance_of_kkt {admm_name})")
    lines.append(f"    [Setting E₁ E₂ F {admm_name} {kkt_name}]")
    lines.append("    [IsOrderedMonoid ℝ]")
    lines.append(f"    ({mu_name} {eps_name} {tau_params} : ℝ)")
    lines.append(f"    ({hp_name} : 1 < {p_name})")
    lines.append(f"    ({r_norm_name} {s_norm_name} : ℕ → ℝ)")
    lines.append(f"    (h_tau_nonneg : ∀ n, 0 ≤ tau_seq {c_name} {p_name} n)")
    lines.append(
        f"    (h_rho : ∀ n, {admm_name}.ρₙ (n+1) = "
        f"update_fun (tau_seq {c_name} {p_name}) "
        f"(dir_seq {mu_name} {eps_name} {r_norm_name} {s_norm_name}) n "
        f"({admm_name}.ρₙ n))"
    )
    lines.append(f"    (fullrank₁ : Function.Injective {admm_name}.A₁)")
    lines.append(f"    (fullrank₂ : Function.Injective {admm_name}.A₂) :")
    lines.append("    ∃ x₁ x₂ y,")
    lines.append(f"  Convex_KKT x₁ x₂ y {admm_name}.toOptProblem ∧")
    lines.append(f"  Tendsto {admm_name}.x₁ atTop (𝓝 x₁) ∧")
    lines.append(f"  Tendsto {admm_name}.x₂ atTop (𝓝 x₂) ∧")
    lines.append(f"  Tendsto {admm_name}.y atTop (𝓝 y) := by")
    lines.append(f"  let tau := tau_seq {c_name} {p_name}")
    lines.append(f"  let dir := dir_seq {mu_name} {eps_name} {r_norm_name} {s_norm_name}")
    lines.append("  have h_dir' : ∀ n, dir n = 1 ∨ dir n = 0 ∨ dir n = -1 := by")
    lines.append(f"    intro n; simpa [dir] using h_dir {mu_name} {eps_name} {r_norm_name} {s_norm_name} n")
    lines.append(f"  let s : AdaptableStrategy (admm := {admm_name}) (admm_kkt := {kkt_name}) :=")
    lines.append("    { tau_seq := tau")
    lines.append("      h_tau_nonneg := h_tau_nonneg")
    lines.append(f"      h_tau_summable := h_tau_summable {c_name} {p_name} {hp_name}")
    lines.append("      update_fun := update_fun tau dir")
    lines.append("      h_update_equiv := h_update_equiv tau dir h_dir' }")
    lines.append(
        f"  apply Strategy3.converges_from_adaptable_strategy "
        f"(admm := {admm_name}) (admm_kkt := {kkt_name}) "
        f"s h_rho fullrank₁ fullrank₂"
    )
    return lines


def _render_generic(_: Dict[str, Any], admm_name: str, kkt_name: str) -> List[str]:
    return [
        "-- generic Strategy3 adapter: caller provides tau_seq/update_fun and proofs",
        "theorem auto_converges",
        f"    ({kkt_name} : Existance_of_kkt {admm_name})",
        f"    [Setting E₁ E₂ F {admm_name} {kkt_name}]",
        "    [IsOrderedMonoid ℝ]",
        "    (tau_seq : ℕ → ℝ)",
        "    (update_fun : ℕ → ℝ → ℝ)",
        "    (h_tau_nonneg : ∀ n, 0 ≤ tau_seq n)",
        "    (h_tau_summable : Summable tau_seq)",
        "    (h_update_equiv : ∀ n rho, 0 < rho →",
        "      update_fun n rho = rho * (1 + tau_seq n) ∨",
        "      update_fun n rho = rho / (1 + tau_seq n) ∨",
        "      update_fun n rho = rho)",
        f"    (h_rho : ∀ n, {admm_name}.ρₙ (n+1) = update_fun n ({admm_name}.ρₙ n))",
        f"    (fullrank₁ : Function.Injective {admm_name}.A₁)",
        f"    (fullrank₂ : Function.Injective {admm_name}.A₂) :",
        "    ∃ x₁ x₂ y,",
        f"      Convex_KKT x₁ x₂ y {admm_name}.toOptProblem ∧",
        f"      Tendsto {admm_name}.x₁ atTop (𝓝 x₁) ∧",
        f"      Tendsto {admm_name}.x₂ atTop (𝓝 x₂) ∧",
        f"      Tendsto {admm_name}.y atTop (𝓝 y) := by",
        f"  let s : AdaptableStrategy (admm := {admm_name}) (admm_kkt := {kkt_name}) :=",
        "    { tau_seq := tau_seq",
        "      h_tau_nonneg := h_tau_nonneg",
        "      h_tau_summable := h_tau_summable",
        "      update_fun := update_fun",
        "      h_update_equiv := h_update_equiv }",
        "  apply Strategy3.converges_from_adaptable_strategy",
        f"    (admm := {admm_name}) (admm_kkt := {kkt_name})",
        "    s h_rho fullrank₁ fullrank₂",
    ]


register_template("residual_balancing", _render_standard)
register_template("generic_strategy3", _render_generic)


def extract_function_source(file_path: str, func_name: str) -> str:
    """
    从 Python 文件中提取指定函数的源码
    """
    src = pathlib.Path(file_path).read_text(encoding="utf-8")
    tree = ast.parse(src)

    for node in tree.body:
        if isinstance(node, ast.FunctionDef) and node.name == func_name:
            # Python 3.8+
            return textwrap.dedent(ast.get_source_segment(src, node))

    raise ValueError(f"Function `{func_name}` not found in {file_path}")


def generate_auto_lean_file_from_file(
    file_path: str,
    stored_file_path: str,
    admm_name="admm",
    kkt_name="admm_kkt",
    file_name="auto_update_rho.lean",
):
    """
    输入: 一个 Python 文件路径，该文件中定义了 update_rho(rho, n)
    输出: Lean4 文件，自动化收敛证明
    """

    # ---- 提取 update_rho 函数源码 ----
    update_rho_src = extract_function_source(file_path, "update_rho")
    tree = ast.parse(update_rho_src)

    # ---- 识别更新形态与模板特征（用于模板选择）----
    ops = set()
    has_rho_keep = False
    has_rho_mul = False
    has_rho_div = False
    has_r_ratio_assign = False
    has_s_ratio_assign = False
    has_mu_compare = False
    has_tau_call = False

    class Visitor(ast.NodeVisitor):
        def visit_Assign(self, node):
            nonlocal has_rho_keep
            nonlocal has_rho_mul
            nonlocal has_rho_div
            nonlocal has_r_ratio_assign
            nonlocal has_s_ratio_assign
            for t in node.targets:
                if isinstance(t, ast.Name) and t.id == "r_ratio":
                    has_r_ratio_assign = True
                if isinstance(t, ast.Name) and t.id == "s_ratio":
                    has_s_ratio_assign = True
            targets = [
                t for t in node.targets if isinstance(t, ast.Name) and t.id == "new_rho"
            ]
            if targets:
                value = node.value
                if isinstance(value, ast.Name) and value.id == "rho":
                    ops.add("keep")
                    has_rho_keep = True
                elif isinstance(value, ast.BinOp):
                    if isinstance(value.left, ast.Name) and value.left.id == "rho":
                        if isinstance(value.op, ast.Mult):
                            ops.add("mul")
                            has_rho_mul = True
                        elif isinstance(value.op, ast.Div):
                            ops.add("div")
                            has_rho_div = True
                        elif isinstance(value.op, ast.Add):
                            ops.add("add")
                        elif isinstance(value.op, ast.Sub):
                            ops.add("sub")
            self.generic_visit(node)

        def visit_Compare(self, node):
            nonlocal has_mu_compare
            left = node.left
            if isinstance(left, ast.Name) and left.id in {"r_ratio", "s_ratio"}:
                if any(isinstance(op, ast.Gt) for op in node.ops):
                    if any(isinstance(c, ast.Name) and c.id == "mu" for c in node.comparators):
                        has_mu_compare = True
            self.generic_visit(node)

        def visit_Call(self, node):
            nonlocal has_tau_call
            if isinstance(node.func, ast.Name) and node.func.id == "tau":
                has_tau_call = True
            self.generic_visit(node)

    Visitor().visit(tree)
    ops.add("keep")
    ordered_ops = [op for op in ["mul", "div", "keep"] if op in ops]
    if not ordered_ops:
        ordered_ops = ["keep"]

    # ---- 模板选择 ----
    template_used = "generic_strategy3"
    if (
        has_rho_mul
        and has_rho_div
        and has_rho_keep
        and has_r_ratio_assign
        and has_s_ratio_assign
        and has_mu_compare
        and has_tau_call
    ):
        template_used = "residual_balancing"

    # ---- 生成 IR 与 LLM Prompt ----
    if template_used == "residual_balancing":
        ir = {
            "tau": {
                "type": "standard",
                "subtype": "p_series",
                "params": ["c", "p"],
                "constraints": [{"name": "hp", "expr": "1 < p"}],
                "lean_expr": "c / Real.rpow ((n : ℝ) + 1) p",
            },
            "dir_logic": (
                "if r_norm_seq n / max (s_norm_seq n) eps > mu then 1 "
                "else if s_norm_seq n / max (r_norm_seq n) eps > mu then -1 else 0"
            ),
            "symbols": {
                "mu": "mu",
                "eps": "eps",
                "r_norm_seq": "r_norm_seq",
                "s_norm_seq": "s_norm_seq",
                "r_ratio": "r_ratio",
                "s_ratio": "s_ratio",
            },
            "proof_obligations": ["tau_summable", "update_equiv"],
            "notes": [
                "uses r_ratio, s_ratio, eps",
                "residual balancing with mul/div/keep",
                f"template_used={template_used}",
            ],
        }
    else:
        ir = {
            "tau": {
                "type": "unknown",
                "params": [],
                "constraints": [],
                "lean_expr": "",
            },
            "dir_logic": "",
            "proof_obligations": ["tau_summable", "update_equiv"],
            "notes": [
                "template_used=generic_strategy3",
                "provide tau/update_fun/h_update_equiv manually or via LLM",
            ],
        }

    render_fn = TEMPLATE_REGISTRY.get(template_used, TEMPLATE_REGISTRY["generic_strategy3"])
    lines = _render_header(admm_name) + render_fn(ir, admm_name, kkt_name)
    file_path_out = pathlib.Path(stored_file_path) / file_name
    with open(file_path_out, "w", encoding="utf-8") as f:
        f.write("\n".join(lines))

    print(f"Lean4 file generated: {file_path_out}")

    # ---- 生成转译报告（保留原始逻辑，标注抽象差异）----
    report_lines = []
    report_lines.append("# Auto Translation Report")
    report_lines.append("")
    report_lines.append("## Source Functions")
    report_lines.append("")
    report_lines.append("### update_rho (Python)")
    report_lines.append("```python")
    report_lines.append(update_rho_src.rstrip())
    report_lines.append("```")
    report_lines.append("")
    try:
        tau_src = extract_function_source(file_path, "tau")
        report_lines.append("### tau (Python)")
        report_lines.append("```python")
        report_lines.append(tau_src.rstrip())
        report_lines.append("```")
        report_lines.append("")
    except ValueError:
        report_lines.append("### tau (Python)")
        report_lines.append("未找到 `tau` 函数。")
        report_lines.append("")
    report_lines.append("## Extracted Operations")
    report_lines.append(f"- template_used: {template_used}")
    report_lines.append(f"- operations: {ordered_ops}")
    report_lines.append(
        "- flags: "
        f"rho_mul={has_rho_mul}, rho_div={has_rho_div}, rho_keep={has_rho_keep}, "
        f"r_ratio={has_r_ratio_assign}, s_ratio={has_s_ratio_assign}, "
        f"mu_compare={has_mu_compare}, tau_call={has_tau_call}"
    )
    report_lines.append("")
    report_lines.append("## Notes on Fidelity")
    report_lines.append("- Lean 侧当前只保留 `mul/div/keep` 三类更新形态。")
    report_lines.append("- 残差驱动分支与连续更新因子目前不会被精确映射。")
    report_lines.append("- 如需更高精度，需要扩展 Lean 策略接口以显式接入残差。")
    report_lines.append("")
    report_file_path = pathlib.Path(stored_file_path) / file_name.replace(".lean", ".report.md")
    with open(report_file_path, "w", encoding="utf-8") as f:
        f.write("\n".join(report_lines))

    print(f"Translation report generated: {report_file_path}")

    ir_file_path = pathlib.Path(stored_file_path) / file_name.replace(".lean", ".ir.json")
    with open(ir_file_path, "w", encoding="utf-8") as f:
        json.dump(ir, f, ensure_ascii=True, indent=2)

    prompt_lines = [
        "System: You are a formal verification expert. Extract the mathematical logic from Python code into JSON for Lean 4.",
        "",
        "Task: Convert the IR below into Lean interface fragments (ONLY define tau_seq/dir_seq/update_fun/h_update_equiv/h_tau_summable).",
        "Do NOT write theorems or imports.",
        "",
        "IR:",
        json.dumps(ir, ensure_ascii=True, indent=2),
        "",
        "Output rules:",
        "1) Only def/lemma, no theorem, no import.",
        "2) Do not introduce new assumptions beyond IR symbols.",
        "3) If proof is hard, use `by` + `admit`.",
    ]
    prompt_file_path = pathlib.Path(stored_file_path) / file_name.replace(".lean", ".prompt.md")
    with open(prompt_file_path, "w", encoding="utf-8") as f:
        f.write("\n".join(prompt_lines))

    print(f"IR generated: {ir_file_path}")
    print(f"Prompt generated: {prompt_file_path}")

if __name__ == '__main__':
    file_dir = "./best_program.py"
    stored_file = "./Optlib/Algorithm/AdaptiveADMM/Strategies/"
    generate_auto_lean_file_from_file(file_path=file_dir, stored_file_path=stored_file)
