# RESULT.md — 变步长 Douglas–Rachford 的 Lean 4 形式化

## 模型与外部帮助来源

- Lean v4.24.0-rc1，mathlib 与 Optlib 使用本地缓存。所有 Lean 检查在 work/ 中以
  `lake env lean <模块>` 与 `lake build` 执行，完整输出与真实退出码保存在 trajectory/run-XX/。
- 题面、下标约定、纸面核对与各阶段候选证明由 Codex 提供（含 run-04/hint-01~03、
  weighted-radius-draft、vertex-mix-draft、ball-perturbation-draft、finite-intersection-draft、
  infinite-ball-draft、minty-draft、resolvent-spec-draft、iteration-draft、step-energy-draft、
  weak-subsequence-draft、scalar-energy-draft、shifted-energy-draft、drs-energy-control-draft、
  adaptive-iteration-draft、graph-limit-draft、adaptive-step-control-draft、weak-algebra-draft、
  weak-pair-draft、weak-uniqueness-draft、drs-residual-helpers、drs-weak-assembly、
  adaptive-connection-draft、drs-convergence-draft、adaptive-final-draft、omega-tail-draft、
  run-26/hint-03/check-file.md）。GLM 5.3 Flash max 完成 Lean 源码写入、修正与各轮源码检查。
  Codex 完成依赖对象构建及最终独立核查。
- 原论文为 [Lorenz–Tran-Dinh 的 arXiv:1801.03765v2](https://arxiv.org/abs/1801.03765v2)。

## 已通过的数学目标

### 基础模块
- Relations.lean（run-03/check-12）：IsMonotoneRel、IsMaximalMonotoneRel、
  IsMonotoneRel.resolvent_unique、IsMonotoneRel.cayley_nonexpansive。
- BallExtension.lean（run-05/check-01、run-06/check-04、run-07/check-02、run-08/check-02）：
  barycenter_variance、barycenter_variance_pairwise、variance_le_weighted_radius、
  ball_objective_nonpos、vertexMix、sum_vertexMix_mul、barycenter_vertexMix、
  vertexMix_mem_stdSimplex、ballObjective、ballObjective_vertexMix、
  finite_ball_intersection、ball_family_intersection。
- Minty.lean（run-09/check-01、run-10/check-02）：IsMaximalMonotoneRel.resolvent_exists
  （Minty 全域性，由极大单调性证明，不作输入）、resolvent_existsUnique、resolvent、
  resolvent_mem、resolvent_eq_of_mem、resolvent_graph、resolvent_nonexpansive。

### 迭代与能量
- Iteration.lean（run-11/check-01、run-12/check-03）：DRState、DRTransition（式 (12) 的
  eqA/eqB）、drStep、drStates、drTraceStep、ExtendedSolution、DRTransition.u_sub_next、
  DRTransition.next_sub_v、DRTransition.energy_descent（式 (17) 单步下降）。
- WeakSubsequence.lean（run-13/check-04）：WeaklyTendsTo、exists_weak_subseq_separable、
  exists_weak_subseq（无可分性假设）。
- ScalarEnergy.lean（run-14/check-03、run-15/check-01、run-19/check-01）：
  energy_le_exp_total、energy_tendsto_of_summable_error、shifted_energy_control、
  conservation_steps_control（保留权重乘法步长的上下界、可求和相邻差与收敛）。

### 收敛
- EnergyControl.lean（run-16/check-01、run-22/check-03）：drs_energy_control、
  state_norm_bounds_of_energy、fixed_coefficient_energy_tendsto、
  norm_tendsto_zero_of_summable_sq、DRTransition.a_add_prev_b_bound。
- GraphLimit.lean（run-18/check-03）：extendedSolution_of_weak_graph_limit。
- WeakAlgebra.lean（run-20/check-05、run-21/check-02）：tendsto_inner_zero_of_eventual_bound、
  WeaklyTendsTo.neg、weaklyTendsTo_of_norm_sub_zero、exists_weak_pair_subseq、
  tendsto_real_of_subseq_subseq、pairEnergy、weak_pair_limit_unique。
- ConvergenceAux.lean（run-23/check-01）：extendedSolution_of_residual_weak_pair、
  drs_fixed_energy_limit。
- Convergence.lean（run-25/check-03）：drs_weak_convergence（Theorem 3.1 全列弱收敛，
  输入仅为原始算法数据：极大单调 A、B、扩展解集非空、步长正下界/上界/可求和差/收敛；
  弱收敛按对全部测试向量的内积收敛表述）、ExtendedSolution.is_zero。

### 自适应式 (21)
- Adaptive.lean（run-17/check-02）：clipRatio（含零分母分支取 hi，含 0/0）、
  clipRatio_bounds、conservationFactor、conservationFactor_pos、AdaptiveState（hy：
  y_n=u_n+t_n b_n）、adaptiveInit（t₀=1，u₀=J_{t₀B}y₀，b₀=(y₀−u₀)/t₀）、adaptiveStep、
  adaptiveStates。
- AdaptiveSpec.lean（run-24/check-01）：adaptive_steps_control、adaptive_state_eq_drStates、
  AdaptiveState.resolvent_y、adaptive_y_step（式 (11) 的尺度化预解形式）、
  adaptive_factor_eq_ratio（ν 等于相邻步长比 t_new/t_old）。
- AdaptiveMain.lean（run-26/check-03）：adaptive_drs_weak_convergence、
  conservationSchedule、conservationSchedule_valid、conservationSchedule_summable、
  adaptiveStatesFromTail、adaptiveStatesFromTail_succ、
  adaptive_drs_weak_convergence_from_tail（用户权重序列从 ω₁ 开始，内部补 ω₀=1，
  不参与递推）。

### 构建与公理核查
- work/DRS.lean 为默认入口（run-26/build-01：lake build 退出 0，仅 linter 警告）。
- work/DRS/AxiomCheck.lean（run-26/check-05 退出 0）：全部主声明
  （resolvent_exists、resolvent_existsUnique、resolvent_nonexpansive、exists_weak_subseq、
  energy_descent、drs_energy_control、extendedSolution_of_residual_weak_pair、
  drs_weak_convergence、adaptive_steps_control、adaptive_state_eq_drStates、adaptive_y_step、
  adaptive_factor_eq_ratio、adaptive_drs_weak_convergence、adaptiveStatesFromTail_succ、
  adaptive_drs_weak_convergence_from_tail）公理依赖均为
  [propext, Classical.choice, Quot.sound]，符合要求；主定理完整类型已打印核对。

## 下标与约定

- 式 (12)：对 n≥0，t=τ_(n+1)；v_(n+1)=J_{tA}(u_n−t b_n)，a_(n+1)=(u_n−t b_n−v_(n+1))/t，
  u_(n+1)=J_{tB}(v_(n+1)+t b_n)，b_(n+1)=(v_(n+1)+t b_n−u_(n+1))/t。对应 DRTransition.eqA
  （v+t•a=u_n−t•b_n）与 eqB（u_(n+1)+t•b_(n+1)=v+t•b_n）。
- 式 (11) 与 (21) 的 y 下标差异：状态恒满足 y_n=u_n+t_n b_n（AdaptiveState.hy）；
  步长比用平滑因子 ν=1−ω+ωκ（adaptive_factor_eq_ratio），不替换为裸 κ。
- 零分母分支：‖y−u‖=0 时 κ 取 κ_max（clipRatio 的 if 分支），包括 0/0。
- 保留权重序列：adaptiveStatesFromTail 以 ωTail 0=ω₁ 开始；内部 conservationSchedule
  补 ω₀=1（不参与任何递推），与原文第一轮 ω₁ 对应。
- 弱极限的算子值符号按 a_(n+1)+b_n→0 处理。b 的弱极限为 w 时，a 的弱极限为 −w。
  两图成员资格由单调性和配对和趋零推出。
- 变度量能量用相邻步长平方差的绝对可求和性控制误差，再用系数极限与有界的对偶距离平方得到固定度量的距离极限。
- 扩展解集非空是原论文证明所用的前提，在 Lean 主定理中显式列出。

## Codex 独立核查

- 按原始题面、论文 §2.2–4 和实际递推逐项复核。核查范围为式 (12)、Theorem 3.1 与式 (21)。
- 单题默认构建和依赖解析通过。严格隐式参数设置下，15 项主要声明的依赖均为 `propext`、`Classical.choice`、`Quot.sound`。
- 在本仓库根目录运行 `lake build DRS DRS.AxiomCheck` 可复现构建与公理输出。完整类型检查见 [AxiomCheck.lean](AxiomCheck.lean)。原生会话和完整检查日志随私有轨迹保存。
