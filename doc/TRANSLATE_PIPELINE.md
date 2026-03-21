# Python → Lean「翻译」流水线说明

本文说明 `lean_admm/alpha_evolve` 里 **如何把自适应 `update_rho` 的 Python 策略接到 Lean4**，以及两条路径的差异。

---

## 1. 总览：两条路径

| 路径 | 脚本 | 是否用 LLM | 输入 | 典型输出 |
|------|------|------------|------|----------|
| **模板路径** | `translate.py` | 否 | `best_program.py`（或任意含 `update_rho` 的文件） | 固定骨架的 `auto_update_rho.lean` + `.report.md` + `.ir.json` |
| **LLM 路径** | `translate_LLM.py` | 是（多轮调用） | 同上 | 数学表述 → 按 `translate_prompt.txt` 生成的 Lean；默认 `auto_update_rho_llm_YYYYMMDD_HHMMSS.lean` |

两条路径的**目标一致**：为 `Optlib` 里 **Strategy3 / AdaptableStrategy** 框架提供可对接的 Lean 策略文件；但 **模板路径不读具体分支逻辑**，只把 Python 源码附在报告里，Lean 正文是预置大模板；**LLM 路径**则尝试把「当前 Python 逻辑」先写成数学表述，再机械翻译成 Lean。

进化评估 **`evaluator.py`** 在数值仿真之外，会走 **LLM 路径里的「数学表述 + R1–R7 检查 + Lean 生成 + `lake env lean`」**（见下文第 4 节）。

---

## 2. 模板路径：`translate.py`

### 2.1 做什么

1. 用 **AST** 从给定 `.py` 文件中抽取 **`update_rho`** 的源码字符串；若存在 **`tau`** 函数也一并抽取。
2. 将写死在 `translate.py` 里的 **`LEAN_TEMPLATE`**（大段 Lean 字符串）中的占位符（如 `$ADMM`、`$KKT`）替换为默认名 `admm` / `admm_kkt`。
3. 把结果写入 `Optlib/Algorithm/AdaptiveADMM/Strategies/auto_update_rho.lean`。
4. 生成 **`auto_update_rho.report.md`**：嵌入抽取到的 Python 源码，便于人工对照。
5. 生成 **`auto_update_rho.ir.json`**：记录所用模板名、备注（如 `h_tau_summable` 等处为占位证明等）。

### 2.2 特点与局限

- **不调用 LLM**，完全确定。
- Lean 正文与 **sample3 类结构**绑定（`tau_seq`、`dir_seq`、`update_fun`、`AdaptableStrategy`、`Strategy3.converges_from_adaptable_strategy` 等）；若真实 `best_program.py` 与模板假设不一致，**数值上能跑通，Lean 侧可能仍需大量手改或补证**。
- 模板内 **`h_tau_summable` 等证明可能是 `sorry` / 宽松占位**，需后续人工或策略库补全。

### 2.3 与项目 readme 的对应关系

对应 readme 里 **Phase 3「模板渲染」** 思路：选固定模板 → 生成 `tau_seq` / `dir_seq` / `update_fun` → 接入 Strategy3；此处模板是 **单一、预置** 的，未做动态 AST→IR→多模板分支。

---

## 3. LLM 路径：`translate_LLM.py`

整体是 **三阶段**（主程序里第二步校验默认注释掉；**evaluator 会三步全开**）。

### 3.1 阶段 A：Python → 数学表述（`get_math_form_from_code`）

- **Prompt**：`build_prompt_code2math`（内嵌在 `translate_LLM.py`）。
- **要求模型输出**：仅用数学符号描述自适应罚参数更新，例如：
  - 序列 \(\{r_k\},\{s_k\},\{\rho_k\},\{\tau_k\}\)；
  - 残差比、阈值 \(\mu_k\)、方向 \(\mathrm{dir}_k\in\{-1,0,1\}\)；
  - \(\rho_{k+1}\) 的分支（乘 \((1+\tau_k)\)、除以 \((1+\tau_k)\)、保持不变）；
  - \(\tau_k\) 与 \(k\)、常数等的关系。
- **约束**：不要编程语法、不要长篇自然语言解释，便于后续形式化。

### 3.2 阶段 B：数学表述 → 是否满足 Strategy3 / C1 式要求（`check_math_form` + `parse_check_result`）

- **Prompt**：`build_prompt_check_code`（内嵌在 `translate_LLM.py`）。
- **角色**：保守的「逻辑检验器」，对照 **R1–R7**（摘要如下）：
  - **R1** \(\tau_k\ge 0\)；**R2** \(\{\tau_k\}\) 可和；**R3** \(\tau_k\) 仅依赖迭代指标 \(k\) 与固定常数（不得依赖 \(r_k,s_k,\rho_k\) 等状态）；
  - **R4** 足够大 \(k\) 后 \(\rho_{k+1}\) 只能是 \(\rho_k(1+\tau_k)\)、\(\rho_k/(1+\tau_k)\)、\(\rho_k\) 之一；
  - **R5** 分支逻辑可依赖残差，但**数值因子**只能是 \((1+\tau_k)\) 及其倒数；
  - **R6** 无 clip、阻尼等后处理；**R7** 确定、良定。
- **输出格式**：严格两行结构——第一块为 R1–R7 每条 `Satisfied`/`Violated` 说明，**最后一行** 为 `True` 或 `False`（当且仅当全部 Satisfied 为 True）。
- **`check_results_formulation(code)`**：对整份 Python 源码字符串先跑阶段 A，再跑阶段 B，返回 `(is_valid, issues, math_form)`。

主程序 `if __name__ == "__main__"` 里 **默认注释掉了 `check_math_form`**，因此单独跑脚本时**不会**因 R1–R7 失败而中断；**evaluator 会调用完整 `check_results_formulation`**，不通过则 **combined_score = 0** 直接淘汰。

### 3.3 阶段 C：数学表述 → Lean4（`get_lean4_results`）

- 读取同目录 **`translate_prompt.txt`**，其中占位符 **`{mathematical_formulation}`** 替换为阶段 A 的数学表述。
- **Prompt 思想**（见文件开头）：**机械翻译**——严格遵循文中的 **SECTION 2 参考示例**（命名、参数顺序、证明骨架、tactic 顺序等），**不得擅自发明、优化或删减**。
- 模型输出可能带 markdown 代码围栏；**`extract_lean_code`** 去掉首行末行 ``` 后得到纯 Lean 文本。
- **落盘**：默认写入 `Optlib/.../Strategies/auto_update_rho_llm_YYYYMMDD_HHMMSS.lean`；环境变量 **`TRANSLATE_LLM_OUT`** 可覆盖路径（见 `LEAN_ADMM_RUN_GUIDE.md`）。

### 3.4 数据流小结（LLM 路径）

```
best_program.py (字符串)
    → [LLM] 数学表述 math_form
    → [LLM，evaluator 必跑] R1–R7 → True/False
    → [LLM] translate_prompt.txt + math_form → Lean 源码
    → 写文件 / print
```

---

## 4. 与 `evaluator.py` 的衔接

对每个进化候选程序 `program_path`：

1. **加载模块**，检查是否存在 **`update_rho`**。
2. 读取源码，调用 **`check_results_formulation(code)`**（阶段 A + B）。
3. 若 **`is_valid` 为 False**：返回 **0 分**，不再跑数值 ADMM，也不再生成 Lean。
4. 若通过： **`run_admm(update_rho)`** 做 LASSO-ADMM 数值评估。
5. 用阶段 A 得到的 **`math_form`** 调用 **`get_lean4_results(math_form)`**，将 Lean 写入临时文件 **`generated_prove_<uuid>.lean`**（在 `Strategies` 目录下）。
6. 在仓库根执行 **`lake env lean <相对路径>`**；若退出码为 0 则认为 **Lean4_Auto_Proven**，否则 **Lean4_Not_Auto_Proven**，并影响综合分数（与迭代次数等组合）。

因此：**翻译逻辑在进化里既是「形式规约门禁」（R1–R7），也是「Lean 代码生成 + 编译验证」**。

---

## 5. 该读哪些文件

| 文件 | 作用 |
|------|------|
| `translate.py` | 模板 `LEAN_TEMPLATE`、`extract_function_source`、`generate_auto_lean_file_from_file` |
| `translate_LLM.py` | `build_prompt_code2math`、`build_prompt_check_code`、`get_lean4_results`、主程序写文件 |
| `translate_prompt.txt` | 阶段 C 的完整指令与参考示例（绑定 Lean 写法） |
| `llm_model.py` | `call_api`（DeepSeek 等） |
| `evaluator.py` | `check_results_formulation`、`get_lean4_results`、`write_unique_lean`、`lake env lean` |

更上层的「IR / 多模板 / VerificationLib」设计见项目根 **`readme.md`**。

---

## 6. 相关运行命令

见 **`doc/LEAN_ADMM_RUN_GUIDE.md`** 第 6 节（`translate.py` / `translate_LLM.py`、环境变量、输出路径）。
