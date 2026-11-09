# AdaRES 形式化结果（RESULT）

## 范围
完成 [Fercoq–Qu（arXiv:1709.02300v1）](https://arxiv.org/abs/1709.02300v1) Algorithm 1（FISTA）、Algorithm 4（AdaRES）与 Theorem 2 的 Lean 4 形式化。入口为 [AdaRES.lean](../AdaRES.lean)，检查模块为 [AxiomCheck.lean](AxiomCheck.lean)。Lean 工具链为 v4.24.0-rc1，复用 mathlib 和本仓库 Optlib、PDAL 的近端存在、唯一性和最优性接口。

## 模块与主要声明
- `Scalar.lean`：动量倒数 `accelInv`、`accelInv_identity`（平方差恒等式）、`accelInv_growth`、`theta` 基本性质、`theta_potential_identity`（势函数用）、`theta_bound`。
- `Prox.lean`：单位二次上界下的 `Smooth` 结构、`objective`、`step`（近端梯度映射）、`lower_tangent`、`step_three_point`（三点不等式）、`step_descent`。
- `Fista.lean`：`fistaNext`/`fistaState`/`fista` 原始三向量递推（θ₀=1、y、x、z 更新）、`fista_scaled_step`（加速势函数单步）、`fista_potential`、`fista_bound`（每块函数值误差 θ_n²/2）、`theta_original`（倒数递推与原文 θ 递推等价）。
- `Threshold.lean`：`period`（正长度约定 `max 1 ⌈2√(e/μ)−1⌉₊`，覆盖原式给零的参数）、`phaseFactor`（θ_(K−1)²/μ ≤ e⁻¹）、`expRounds`（零误差直接取 1）、`estimate`（μ₀/2^s 半减）、`goodStage` 及其与估计值 μ_s ≤ μ_F 的等价。
- `Geometry.lean`：梯度 cocoercivity、Lipschitz 常数 1、近端梯度步非扩张性、单位近端非扩张性。
- `ErrorBounds.lean`：`Minimum`（任意最优点存在性输入）、`solutions`（整个最优解集）、`residual`、`LocalGrowth`（相对整个最优解集的 infDist，局部二次增长作为假设输入，真实 μ_F 只用于终止证明）、目标函数次水平集闭性（lsc 仅经闭次水平集使用，有效域不假定闭）、`nearest_solution`、`residual_le_gap`（R ≤ 2Δ）、`gap_step_le_residual`（Δ(Tx) ≤ 8R(x)/μ_F，使用 T 最优性的特定次梯度，不假定所有次梯度范数有界）、`fista_descent`、`fista_gap_bound`（FISTA 块误差用最近最优解）。
- `Stages.lean`：`RestartParams`、`phasePoint`（阶段起点为 T(前驱点)）、`blockStop`（阈值超调或残差 ≤ ε 的析取停止条件）、`blockStop_exists`（由 `expRounds` 保证）、`firstBlocks`（真实递推取 Nat.find 最小正索引，非输入）、`phase_invariant`、`previous`（阶段前驱递推）、`stageBlocks`、`stageSuccess`、`previous_invariant`。
- `Restart.lean`：`phase_gap_decay`、`good_threshold`、`good_residual_bound`（好阶段残差指数衰减）、`good_stage_succeeds`（估计值 ≤ μ_F 的阶段必成功）、`stage_exists`（首个成功阶段由 `goodStage` 上界存在性构造）、`firstStage`（Nat.find 最小索引）、`resultPoint`（T(末前驱点)）、`callCount`（1+∑(t_s K_s+1)，Remark 7 缓存求值）、`result_spec`（最小阶段、逐阶段最小性、返回点残差与函数值界 Δ(x̂) ≤ 8ε/μ_F）。
- `Count.lean`：`earlyRounds`（32Δ/(εμ_F) 取整）、`goodRounds`（2Δ/ε 取整）、早期阶段块数界 U 与好阶段块数界 V、`cached_block_count`（每阶段 t·K_s+1 的缓存计数等式）、`callCount_bound`（全输入有限和界，末阶段 +1 项由正 V 与上取整余量覆盖，未删去）、正 μ₀<4e 时 `period_original`（块长为原式）、`expRounds_original`（次数为原式）、几何和 `sum_period_bound`（√(e/μ_s)=√(e/μ₀)(√2)^s 经 `Real.sqrt_mul`、`sqrt_two_pow`）。
- `PaperCount.lean`：`callCount_eq34`（μ₀ ≤ μ_F 时 N̂ ≤ K₀⌈ln(2Δ/ε)⌉+2）、`callCount_eq35`（μ₀ > μ_F 时完整式 (35)，含末阶段 ⌈2√(2e/μ_F)⌉V 项与 1+Σ 常数项）。印刷范围条件：块长为正需 μ₀ < 4e；对数次数至少 1 的条件 hU/hV 用于去掉保护 max 1；Δ=0 由 `expRounds` 取 1，不套用会小于一次重启的印刷界。
- `Transform.lean`：正对角 `diagonalEquiv`（√L 坐标缩放）、范数对应 `diagonal_norm_sq`（加权范数=欧氏范数）、配对对应 `diagonal_pairing`、`normalizeSmooth`（二次上界对应）、`normalizeRegularizer`（proper l.s.c. 凸 ψ 对应，lsc 经连续原像）、`weightedStep`、`weightedStep_spec`（加权 T 的存在、加权模型最小性与由 `prox_scale_unique` 加单射性推出的唯一性）。
- `Weighted.lean`：加权目标、最优解集、残差（加权平方范数）、`WeightedLocalGrowth`（经 B 的像集距离）、域/目标/解集/间隙/残差/增长的归一化对应、原坐标 FISTA 状态 `weightedFistaState_next`（x′=weightedStep y，z′=z+θ⁻¹(x′−y)）、阶段点与前驱点、原坐标阈值常数 16·weightedResidual/μ 与停止等价 `weighted_blockStop_eq`、`weighted_blocks_spec`（正块数、末点停止、逐块最小性）、`weighted_stageSuccess_eq`（阶段 s 测试点为 weightedPrevious (s+1)）、`weighted_stage_exists`、主定理 `weighted_main`：返回点等式、最小阶段索引、逐阶段最小性、测试点残差 ≤ ε、返回点残差 ≤ ε、函数值界 ≤ 8ε/μ_F、调用数等式与全输入界。真实 μ_F 仅出现在终止与界的证明中，算法定义不输入增长常数。

## 印刷边界处理
- 块长正长度约定 `period = max 1 ⌈2√(e/μ)−1⌉₊`：μ ≥ 4e 时原式 ≤ 0，取 1；原式为正时（μ < 4e）`period_original` 证明与原式一致且 K_s+1 = ⌈2√(e/μ_s)⌉。
- 对数次数 `expRounds` 在 A=0 时取 1，此时原对数式无定义。A>0 且 ⌈ln(A/ε)⌉ ≥ 1 时，`expRounds_original` 证明与原式一致。
- 调用数保留 `1+Σ(t_sK_s+1)` 与末阶段 +1 项；式 (35) 的末阶段用 `period μ_S + 1 = ⌈2√(e/μ_S)⌉ ≤ ⌈2√(2e/μ_F)⌉` 与 V ≥ 1 收尾。
- 首个成功阶段索引由 `Nat.find` 从真实停止谓词构造，其 ≤ goodStage 由 `good_stage_succeeds` 与 `Nat.find_min'` 证明，非输入。

## 独立核查

Codex 独立核对了默认构建、实际依赖解析和 19 项主要声明。公理依赖在
`propext`、`Classical.choice`、`Quot.sound` 范围内。在本仓库根目录运行
`lake build AdaRES AdaRES.AxiomCheck` 可复现构建与公理输出。原生会话和完整检查日志随私有轨迹保存。

## 帮助来源
- Codex 提供模块候选及局部诊断。GLM 用原生文件工具写入数学源码，并按 Lean 日志修正。
- 近端接口复用 adgd_publication 提交 a0b265a 的 Optlib（`Convex_first_order_condition'`、`convex_to_lower`、`lower_to_lipschitz`、`gradient_norm_sq_eq_two_self`）与 PDAL.Definitions（`ProperConvex`、`prox`、`prox_optimality`、`prox_scale_unique`、`cosine_rule`）。
- 调用数依据原论文 Remark 7 的求值复用顺序，边界处理核对了 Theorem 2 的式（34）、（35）、（39）和（40）。
- GLM 5.3 Flash max 完成本题的数学源码写入、修正和原生检查。调用数是论文 Remark 7 所述求值顺序的数学计数。
