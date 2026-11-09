# UFGM 形式化 RESULT（run-01 至 run-09）

## 交付范围

对 Nesterov 公开稿 CORE 2013/26 §4 的 Universal Fast Gradient Method（式 4.1–4.5 与 Theorem 3）完成 Lean 4.24.0-rc1 + Mathlib 形式化。保留任意有限维实赋范空间 E（无内积结构）、连续线性对偶、任意非空闭凸 Q、凸 f 在 Q 上的选定次梯度、proper l.s.c. 扩展实值凸 Ψ、1-强凸 Bregman 核 d 与原始极小点 x₀（允许 x₀ 在 dom Ψ 之外）。

## 相对 Q 的 Bregman 导数条件

- 核的导数 `Kernel.derivative` 是相对 Q 的 Fréchet 导数：`∀ x ∈ Q, HasFDerivWithinAt value (derivative x) Q x`（UFGM/Kernel.lean）。不假设全局可微。
- 若核仅在相对内部可微，题面要求说明边界基点的定义；本实现直接把 `HasFDerivWithinAt` 在整个 Q 上成立作为核数据的一部分（`Kernel.hasDerivative`），即边界点也带相对导数，因此不需要单独的边界论证，也不能直接套用只在内部可微的核。Bregman 基点（estimateMin、trialU 的构造中出现的基点）都落在 Q 内，其相对导数由该字段给出。
- `min_bregman_support` 证明最小点处 `d.value v + G v + bregman d v w ≤ d.value w + G w`，只用相对导数沿 Ioc(0,1) 线段的右差商极限，不要求正则项可微。

## L₀ 常数修正与反例

- 主率定理 `main_rate` 使用 D = max(L₀, 2C)，C = M^(2/(1+ν))·ε^(−p)，p = (1−ν)/(1+ν)。这保留任意初始估计 L₀ > 0。
- 仅在附加前提 `L0 ≤ 2 * smoothConstant ν M ε` 下恢复原文印刷常数：`paper_rate`（式 4.3 系数 `(2^(2+4ν)·M²/(ε^(1−ν)·n^(1+3ν)))^(1/(1+ν))`）、`paper_rounds` 与 `paper_target_accuracy`（式 4.5 轮数 `(2^((3+5ν)/2)·M/ε)^(2/(1+3ν))·ξ^((1+ν)/(1+3ν))` 上取整，至少一轮）。
- 式（4.3）的印刷常数对任意 L₀ 可失效。Codex 给出的纸面反例取 E=ℝ，f(x)=x²/2，Ψ(x)=8(x−1)²，d(x)=x²/2，x₀=0，L₀=256，ε=M=ν=1。首轮 τ=1、a=1/256，接受 y₁=1/17，最优点 16/17。目标差 225/34 大于印刷上界 1024/289+1/2。该反例为纸面核对。一般初值的主率及轮数用 D=max(L₀,2C)。 [原论文](https://optimization-online.org/wp-content/uploads/2013/04/3833.pdf)

## 已检查范围（全部通过 Lean 核心检查，仅依赖 propext、Classical.choice、Quot.sound）

- TrialScalar：试探正根 `trialWeight`、唯一性、`trialRatio` 范围/倒数/单调、大 H 下 `trialWeight_small`。
- Holder：从选定次梯度的 Hölder 条件证式（2.5）`holder_model`，ν=0 用两端支持，ν>0 用相对线段导数与单调性界；不引入 f 全局可微。
- ModelBound：`young_holder` 加权算术几何平均、容差模型 `tolerance_model`（H·τ^p ≥ C 时接受）；ν∈[0,1]、M=0 覆盖。
- TrialBound：`scaledTrial`（即 Hτ^p）公式、下界、`threshold_candidate_exists`（有限二分试探保证候选存在）、首试单调。
- StateTrial：原始状态与估计序列（A=0 时域为 Q，φ₀(x)=ξ(x₀,x)，最小点 x₀；A>0 时域为 dom Ψ）、试探点 x、近端点 u、试探输出 z、接受谓词 `Accept`、`accept_of_threshold`。
- Iteration：`accept_exists` 有限终止、`acceptedIndex` 最小非负索引（不读取 ν、M 数值）、`next` 的原始 φ 更新（A、L=H/2、y=z、lin、constant）、M=0 时 `accepted_zero_constant`（每轮首试接受）。
- Curvature：`uniform_curvature` 统一界 Hτ^p ≤ D=max(L₀,2C)（正次回溯用前一候选失败与 τ 随 H 不增；首试接受用新累计权与上轮已接受曲率）、`states_growth` 累计权下界 A_k ≥ (k/2)^(1/γ)/D，γ=1/(2−p)=(1+ν)/(1+3ν)。
- Estimate：估计序列双不变量 `estimate_lower`（A_k(F(y_k)−ε/2) ≤ min φ_k）与 `estimate_upper`（φ_k(w) ≤ ξ(x₀,w)+A_k·F(w)，ξ=0 覆盖）。
- Main：`main_rate` 间隙界（ε/2 + D·ξ(w)/(k/2)^(1/γ)）、`target_accuracy` 轮数上界（含自然数上取整与至少一轮 `max 1`）。
- PaperConstants：`paper_rate_coeff_eq`、`paper_round_threshold_eq` 两个印刷常数恒等式及三条 L₀≤2C 推论 `paper_rate`、`paper_rounds`、`paper_target_accuracy`。

## 帮助来源

- Codex 提供题面、算法结构与候选证明稿。GLM 5.3 Flash max 用原生文件工具写入、修正数学源码并执行 Lean 检查。
- Mathlib 接口核对：`pow_unbounded_of_one_lt`（Mathlib.Algebra.Order.Archimedean.Basic，需 `[ExistsAddOfLE]` 实例显式 `(R := ℝ)`）、`Real.geom_mean_le_arith_mean2_weighted`、`IsMinOn.of_isCompact_preimage`、`antitoneOn_of_hasDerivWithinAt_nonpos`、`hasDerivWithinAt_iff_tendsto_slope'`。

## Codex 独立核查

Codex 独立核对了默认构建、实际依赖解析和 23 项主要声明。每项只依赖
`propext`、`Classical.choice`、`Quot.sound`。在本仓库根目录运行
`lake build UFGM UFGM.AxiomCheck` 可复现构建与公理输出。
完整类型检查见 [AxiomCheck.lean](AxiomCheck.lean)。原生会话和完整检查日志随私有轨迹保存。
