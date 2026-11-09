import AdaRES

open AdaRES

-- 标量引理
#check @AdaRES.theta_original
#check @AdaRES.accelInv_identity
#check @AdaRES.theta_potential_identity
#check @AdaRES.theta_bound

-- 近端梯度
#check @AdaRES.step_three_point
#check @AdaRES.step_descent
#check @AdaRES.step_nonexpansive
#check @AdaRES.gradient_lipschitz

-- FISTA 势函数
#check @AdaRES.fista_scaled_step
#check @AdaRES.fista_potential
#check @AdaRES.fista_bound

-- 阈值与次数
#check @AdaRES.phaseFactor_le
#check @AdaRES.expRounds_bound
#check @AdaRES.goodStage_iff

-- 误差界与几何
#check @AdaRES.nearest_solution
#check @AdaRES.residual_le_gap
#check @AdaRES.gap_step_le_residual
#check @AdaRES.fista_gap_bound
#check @AdaRES.good_threshold
#check @AdaRES.good_residual_bound

-- 阶段递推与重启
#check @AdaRES.firstBlocks_spec
#check @AdaRES.firstBlocks_minimal
#check @AdaRES.good_stage_succeeds
#check @AdaRES.stage_exists
#check @AdaRES.result_spec

-- 调用数
#check @AdaRES.cached_block_count
#check @AdaRES.callCount_bound
#check @AdaRES.callCount_eq34
#check @AdaRES.callCount_eq35

-- 坐标变换与加权
#check @AdaRES.diagonal_norm_sq
#check @AdaRES.diagonal_pairing
#check @AdaRES.weightedStep_spec
#check @AdaRES.normalized_residual
#check @AdaRES.weightedFistaState_next
#check @AdaRES.weighted_blocks_spec
#check @AdaRES.weighted_stageSuccess_eq
#check @AdaRES.weighted_stage_exists
#check @AdaRES.weighted_main

#print axioms AdaRES.theta_original
#print axioms AdaRES.step_three_point
#print axioms AdaRES.step_nonexpansive
#print axioms AdaRES.nearest_solution
#print axioms AdaRES.gap_step_le_residual
#print axioms AdaRES.fista_gap_bound
#print axioms AdaRES.phaseFactor_le
#print axioms AdaRES.firstBlocks_spec
#print axioms AdaRES.firstBlocks_minimal
#print axioms AdaRES.good_stage_succeeds
#print axioms AdaRES.stage_exists
#print axioms AdaRES.result_spec
#print axioms AdaRES.cached_block_count
#print axioms AdaRES.callCount_bound
#print axioms AdaRES.callCount_eq34
#print axioms AdaRES.callCount_eq35
#print axioms AdaRES.diagonal_norm_sq
#print axioms AdaRES.weightedStep_spec
#print axioms AdaRES.weighted_main
