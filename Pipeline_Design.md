# ADMM 自适应策略转译流水线（整理版）

## 目标
LLM 搜索得到 `best_program.py` 中的自适应步长/更新策略，自动转译为 Lean4 接入代码，并复用既有收敛性证明框架完成验证。

---

## Phase 1: Lean 基础设施（Safety Net）
文件：`Optlib/Algorithm/AdaptiveADMM/Strategies/VerificationLib.lean`

**目的**：提供可复用的“乐高积木”定理，避免每次让 LLM 从零发明证明。

**模板定理**
- **L1 P-级数收敛（标准 decay）**
  - 形式：`c / (n+1)^p`，需 `p > 1`
- **L2 几何级数收敛（指数 decay）**
  - 形式：`c * r^n`，需 `0 ≤ r < 1`
- **通用工具：最终相等引理**
  - 若 `f` 在某个 `N` 之后与 `g` 相等且 `g` 可和，则 `f` 可和。

---

## Phase 2: LLM 语义解析（The Brain）
目标：LLM 从 Python 代码中抽取策略逻辑，输出严格 JSON IR。

### 任务 1：分类 tau（步长）
- **standard**：匹配 `c/(n+1)^p` 或 `c*r^n`
- **piecewise**：存在 `if k < N` 结构，提取 cutoff 与稳定表达式
- **complex**：复杂表达式，提供可证明上界 `upper_bound`

### 任务 2：提取更新方向
输出 `dir_logic`，映射为 `{1, -1, 0}` 的分支逻辑（Lean if-then-else 形式）。

### IR Schema
```json
{
  "tau": {
    "type": "standard | piecewise | complex",
    "params": ["c", "p"],
    "constraints": ["1 < p"],
    "lean_expr": "...",
    "cutoff": 100,
    "stable_lean_expr": "...",
    "upper_bound": "..."
  },
  "dir_logic": "if r / max s eps > mu then 1 else ..."
}
```

---

## Phase 3: Python 胶水（translate.py 渲染）
文件：`translate.py`

**职责**：接收 IR，渲染 Lean 代码文件。

### 生成流程（核心）
1. 选择模板（基于 AST/IR）
2. 生成 `tau_seq`、`dir_seq`、`update_fun`
3. 自动构造 `h_tau_summable`：
   - **standard**：调用 `p_series_summable_template` 或 `geometric_summable_template`
   - **piecewise**：通过“最终相等”把尾部收敛转移给整体
   - **complex**：尝试比较判别（可能需要 `sorry` 或额外不等式）
4. 封装 `AdaptableStrategy`，接入 Strategy3 收敛定理

---

## 策略复杂度分级
| 级别 | 类型 | 方法 | 预期成功率 |
|---|---|---|---|
| L1 | 标准型 (P-series/Geometric) | 模板库直接调用 | 99% |
| L2 | 分段型 (Piecewise) | 分解 + Tail 收敛 | 90% |
| L3 | 有界复杂型 (Complex) | 比较判别法 | 70% |
| L4 | 未知型 (Unknown) | Tactic + Sorry | 低 |

---

## 关键要点
1. **Lean 证明固定化**：将收敛性证明完全交给 `VerificationLib` + `Strategy3` 框架。
2. **LLM 输出必须结构化**：只允许 JSON IR，禁止直接生成完整 Lean。
3. **模板优先 + LLM 兜底**：满足模板走确定性路径，不满足走 LLM。

---

## 下一步建议
- 为 L2/L3 提供更强的自动证明工具（例如更多比较判别模板）
- 将 LLM prompt 固化，限制输出范围，减少 Lean 端不确定性
