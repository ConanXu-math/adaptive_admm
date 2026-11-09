# APDAL 形式化结果报告

## 原始范围

复用本仓库的 PDAL、Optlib 与 mathlib，在有限维实内积空间上完成
[Malitsky–Pock（arXiv:1608.08883v2）](https://arxiv.org/abs/1608.08883v2) §3.1 的
Algorithm 2、式 (35)–(40) 与 Theorem 4 的 Lean 4 形式化。

## 已证明内容（全部通过 Lean 类型检查）

1. `Scalar.lean`：标量增长定理。β₀>0、γc>0 且 β_{n+1} ≥ β_n + γc√β_n 时，
   取 b = min(β₀, (γc/3)²) > 0，对所有 n 有 β_n ≥ b(n+1)²。
2. `Iteration.lean` 给出 Algorithm 2 的递归构造。`State` 编号 n 存放 x_n、y_(n+1)、
   τ_n、β_n、θ_n、试探步长与接受索引。`Params` 保留任意合法试探选择器。
   `next` 用最小接受索引 `min_accept_index`（δ=1）构造下一状态。
   `next_accept`、`next_minimal` 给出接受与最小性规格。
   另含 K=0 时每个候选都接受（`accept_cond_of_K_zero`）与候选对偶增量为零
   时该候选接受（`accept_cond_of_zero_dual`）。
3. `EnergyLocal.lean`：式 (35) 的单步能量不等式。由 g 的强凸次梯度支持
   （`StrongSupport`）、近端最优性与 δ=1 接受条件推出，含额外项
   β‖x̄−v‖²/2。
4. `Growth.lean`：步长下界 c = min(q₀, μ/(1+‖K‖)) > 0（零次回溯用试探下端、
   正次回溯用前一候选失败，覆盖 K=0），加权步长不等式
   σ_{k+1}θ_{k+1} ≤ σ_k(1+θ_k)，以及 β 与 s_N 的二次增长下界。
5. `Weights.lean`：非负权 `ergWeight` 的望远求和恒等式，同时给出总权、
   原平均分子与函数值求和，不要求外推点在有效域。
6. `Energy.lean`：能量定义 `energy sp s k` 读取 `(s k).beta·‖x_k−x̂‖²/2 +
   ‖(s (k−1)).y−ŷ‖²/2`，即 E_k 的对偶部分取 `states (k−1).y`（因 `states k`
   存放 y_(k+1)）。`state_energy` 把局部能量接到原始递归；
   `energy_sum_from` 望远求和。
7. `Averages.lean` 给出原平均点 X_N、Y_N 的定义域。X_N 是原始迭代点 x₁ 至 x_N
   的非负权凸组合，Y_N ∈ dom h。另证间隙非负、原式 (39) 的 x₀∈dom g 联合界（保留确切
   初始项），以及任意 x₀ 的有限常数界（常数只用 states 1 的近端函数值，
   不用域外函数值）。
8. `Main.lean`：Theorem 4 两条速率。对任意初始点与合法选择器，存在
   C₁ = √(2C/b)、C₂ = C/d ≥ 0，对所有 N ≥ 1：
   ‖x_N−x̂‖ ≤ C₁/N 且 0 ≤ G(X_N,Y_N) ≤ C₂/N²。

## 纸面修正

- 本题证明 s_N 的 Ω(N²) 下界。原文的二次上界在合法选择器下可不成立。
  例如 K=0、γτ₀=1，每轮试探 τ₀，则 θ_k=1 且 β_k 每轮乘 2。
- `states k` 的 y 字段对应论文 y_(k+1)，故 E_k 的对偶项读取
  `states (k−1).y`。
- 任意初始化常数只用 states 1 的原始点函数值与对偶间隙，x₀ 不需要
  属于 dom g。

## 实际检查

Codex 独立核对了默认构建、实际依赖解析和 19 项主要声明。公理均为
`propext`、`Classical.choice`、`Quot.sound`。在本仓库根目录运行
`lake build APDAL APDAL.AxiomCheck` 可复现构建与公理输出。
完整类型检查见 [AxiomCheck.lean](AxiomCheck.lean)。原生会话和完整检查日志随私有轨迹保存。

## Codex/GLM 帮助来源

- Codex 提供未检查候选：scalar-candidate、iteration-candidate、
  energy-local-candidate、growth-candidate、weights-candidate、
  energy-connection-candidate、averages-candidate、main-rate-candidate，
  以及诊断（energy-index-diagnosis、audit-coverage）。
- GLM 写入本题数学源码、按完整 Lean 日志修正（如 InnerProductSpace 记号
  open、能量对偶索引改为 states (k−1).y、Weights 求和括号、K=0 接受
  引理的范数化简等），并执行原生构建、类型与公理检查。上文单列 Codex 独立核查。
