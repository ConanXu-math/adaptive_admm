import json
import os
from alpha_evolve.llm_model import call_api


# ======================================================
# Initialize LLM client
# Make sure the environment variable is set:
# export OPENAI_API_KEY="your_api_key_here"
# ======================================================
class LLMClient:
    def __init__(self, model_name: str = "deepseek"):
        self.model = model_name

    def generate(self, prompt: str, system_prompt: str) -> str:
        return call_api(self.model, prompt, system_prompt)


# ======================================================
# Read Python source code from file
# ======================================================
def read_source_code(path: str) -> str:
    with open(path, "r", encoding="utf-8") as f:
        return f.read()


# ======================================================
# Build the prompt (strictly follows the given prompt)
# ======================================================
def build_prompt_code2math(code: str) -> tuple[str, str]:
    system_prompt = f"""You are a formal reasoning expert familiar with optimization theory and rigorous algorithm specification."""
    message = f"""I will give you a piece of Python code implementing an **adaptive penalty update rule** for the ADMM algorithm.  

Your task is to translate the logic into **concise, minimal mathematical language**, suitable for use in formal verification systems like Lean4.

### Your Output Must:

1. Define all sequences formally:  
   Use mathematically indexed notation like \\( \\{{r_k\\}}, \\{{s_k\\}}, \\{{\\rho_k\\}}, \\{{\\tau_k\\}} \\), etc.

2. Include the following components:
    - Residual ratios, such as \\( r_k / \\max(s_k, \\varepsilon) \\), and symmetrically for \\( s_k \\)
    - An adaptive threshold value \\( \\mu_k \\), possibly dependent on \\( k \\) or residual scaling
    - A direction function \\( \\text{{dir}}_k \\in \\{{-1, 0, 1\\}} \\) based on residual imbalance
    - A recurrence rule like:
      \\[
      \\rho_{{k+1}} =
      \\begin{{cases}}
      \\rho_k \\cdot (1 + \\tau_k), & \\text{{if }} \\frac{{r_k}}{{s_k}} > \\mu_k \\\\
      \\rho_k / (1 + \\tau_k), & \\text{{if }} \\frac{{s_k}}{{r_k}} > \\mu_k \\\\
      \\rho_k, & \\text{{otherwise}}
      \\end{{cases}}
      \\]

3. Define all auxiliary functions, such as:
    - \\( \\tau_k \\), in terms of iteration index \\( k \\), residuals \\( r_k, s_k \\), and parameters \\( c, p \\), possibly using:
      \\[
      \\tau_k := \\phi\\left( \\log(1 + \\text{{excess}}) \\right) \\cdot c / (k+1)^p
      \\]
      where excess is a normalized residual ratio.

4. **Avoid any programming syntax**—use only mathematical definitions with properly defined terms.

5. Do **not** generate code or explain in natural language—just output the minimal and exact set of formulas that define the update logic in a form ready for formalization in a proof assistant.

Here is the Python code for reference:

```python
{code}"""
    return system_prompt, message


def build_prompt_check_code(math_form: str) -> tuple[str, str]:
    system_prompt = (
        "You are a STRICT and CONSERVATIVE mathematical verifier for adaptive ADMM penalty update rules.\n\n"
        "Your role is ONLY to CHECK correctness.\n"
        "You must NOT suggest improvements, alternatives, or fixes.\n\n"
        "You must decide whether a given mathematical specification\n"
        "satisfies the Strategy3 / Condition C1 requirements\n"
        "used in convergence proofs of adaptive ADMM.\n\n"
        "IMPORTANT RULES:\n"
        "- Be maximally conservative.\n"
        "- If ANY requirement is violated, unclear, implicit, or ambiguous, the result MUST be False.\n"
        "- If a requirement is not EXPLICITLY satisfied in the specification, treat it as violated.\n"
        "- Do NOT assume standard practice or intent.\n"
    )

    message = f"""You are given a mathematical specification of an adaptive ADMM penalty update rule.

    Your task is to VERIFY whether it satisfies ALL Strategy3 / Condition C1 requirements.

    You are a FORMAL LOGICAL VERIFIER.
    You must follow the rules EXACTLY as stated.
    You are NOT allowed to debate, speculate, self-correct, or revise decisions.

    You MUST evaluate EACH requirement R1–R7 INDEPENDENTLY.

    ---

    REQUIREMENTS:

    R1. Nonnegativity of tau_k (GLOBAL):
        tau_k ≥ 0 for ALL k ∈ ℕ.

    R2. Summability of tau_k (GLOBAL):
        The sequence {{tau_k}} is summable:
            ∑_(k=0)^∞ tau_k < +∞.

    R3. Independence of tau_k (GLOBAL):
        tau_k MUST be an explicit function ONLY of:
            - the iteration index k, and
            - fixed constants (including thresholds such as K₀).

        Piecewise definitions are ALLOWED
        IF tau_k is explicitly defined for ALL k ∈ ℕ.

        tau_k MUST NOT depend on:
            r_k, s_k, rho_k,
            residual ratios,
            adaptive counters,
            or ANY state-dependent quantity.

    R4. Allowed rho updates (EVENTUAL):
        There exists K₀ such that for ALL k ≥ K₀,
        rho_(k+1) is EXACTLY one of:
            (a) rho_k · (1 + tau_k)
            (b) rho_k / (1 + tau_k)
            (c) rho_k

        No other functional form is allowed for k ≥ K₀.
        Finite violations for k < K₀ are ALLOWED.

    R5. Separation of logic and magnitude (EVENTUAL):
        For ALL k ≥ K₀:

        • The LOGIC selecting the update case
          (multiply / divide / keep)
          MAY depend on r_k and s_k.

        • The NUMERIC UPDATE FACTOR
          MUST be EXACTLY (1 + tau_k) or its reciprocal.

        • The numeric update factor MUST depend ONLY on tau_k
          and MUST NOT depend on r_k, s_k, ratios, thresholds,
          counters, or any other quantity.

    R6. No post-processing of rho (EVENTUAL):
        For ALL k ≥ K₀, the update MUST NOT include:
            - clipping or projection,
            - min / max bounds,
            - normalization,
            - smoothing or averaging,
            - damping or correction factors,
            - or ANY modification applied AFTER
              the update formula.

        Finite violations for k < K₀ are ALLOWED.

    R7. Determinism and well-definedness (EVENTUAL):
        For ALL k ≥ K₀, the update rule MUST be:
            - deterministic,
            - fully specified for all valid inputs,
            - free of undefined expressions,
            - free of branching ambiguity.

    ---

    INPUT SPECIFICATION (to be checked):

    <<<
    {math_form}
    >>>

    ---

    DECISION PROTOCOL (MANDATORY):

    • For EACH requirement R1–R7, you MUST output EXACTLY ONE judgment:
          "Satisfied" OR "Violated".

    • Once a judgment for Ri is made, it MUST NOT be contradicted
      or revised anywhere else in the output.

    • Line 2 ("True" or "False") MUST be computed STRICTLY as follows:
          - Output "True" IF AND ONLY IF ALL R1–R7 are "Satisfied".
          - Output "False" IF AND ONLY IF AT LEAST ONE Ri is "Violated".

    • You are NOT allowed to choose Line 2 independently of Line 1.

    ---

    OUTPUT FORMAT (STRICT — FOLLOW EXACTLY):

    Return EXACTLY TWO lines.
    Do NOT output anything else.
    
    Line 1:
    A COMPLETE and EXHAUSTIVE report for ALL requirements R1–R7,
    using EXACTLY the following structure:

    R1: <Satisfied / Violated>. <Concise explanation>
    R2: <Satisfied / Violated>. <Concise explanation>
    R3: <Satisfied / Violated>. <Concise explanation>
    R4: <Satisfied / Violated>. <Concise explanation>
    R5: <Satisfied / Violated>. <Concise explanation>
    R6: <Satisfied / Violated>. <Concise explanation>
    R7: <Satisfied / Violated>. <Concise explanation>

    Do NOT omit any requirement.
    Do NOT merge requirements.
    Do NOT use bullet points.
    Do NOT add commentary.
    Do NOT restate the full specification.

    Line 2:
    True or False

    """
    return system_prompt, message


def get_math_form_from_code(code: str, client: LLMClient) -> str:
    system_prompt, message = build_prompt_code2math(code)
    mathematical_formulation = client.generate(message, system_prompt)
    return mathematical_formulation


def check_math_form(math_form: str, client: LLMClient) -> str:
    system_prompt, message = build_prompt_check_code(math_form)
    check_results = client.generate(message, system_prompt)
    return check_results


def parse_check_result(check_result: str) -> tuple[bool, str]:
    lines = [l.strip() for l in check_result.splitlines() if l.strip()]
    if not lines:
        return False, "Empty checker output"

    is_valid = lines[-1] == "True"
    issues = lines[0:-1] if len(lines) > 1 else ""

    return is_valid, issues


def check_results_formulation(code: str):
    client = LLMClient()
    math_form = get_math_form_from_code(code, client)
    check_result = check_math_form(math_form, client)
    is_valid, issues = parse_check_result(check_result)
    return is_valid, issues, math_form


def get_lean4_results(mathematical_formulation: str) -> str:
    client = LLMClient()
    system_prompt = f"""You are a **Lean 4 code generator**, not a mathematician and not a tutor."""
    prompt_path = os.path.join(os.path.dirname(__file__), "translate_prompt.txt")
    with open(prompt_path, "r", encoding="utf-8") as f:
        prompt = f.read()
    prompt = prompt.replace("{mathematical_formulation}", mathematical_formulation)
    lean4_results = client.generate(prompt, system_prompt)
    lean4_results = extract_lean_code(lean4_results)
    return lean4_results


def extract_lean_code(text: str) -> str:
    lines = text.splitlines()
    if lines and lines[0].startswith("```"):
        lines = lines[1:]
    if lines and lines[-1].startswith("```"):
        lines = lines[:-1]
    return "\n".join(lines)


if __name__ == "__main__":
    python_code = read_source_code(os.path.join(os.path.dirname(__file__), "./openevolve_output/best", "best_program.py"))
    # python_code = read_source_code(os.path.join(os.path.dirname(__file__), "initial_program.py"))
    llm = LLMClient()
    mathematical_formulation = get_math_form_from_code(python_code, llm)
    # check_results = check_math_form(mathematical_formulation, llm)
    lean4_results = get_lean4_results(mathematical_formulation)
    print(lean4_results)

