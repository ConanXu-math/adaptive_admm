import APDAL

/-!
# 交付核查：完整类型与公理

按 audit-coverage 范围打印主要声明完整类型与公理。
只允许依赖 propext、Classical.choice、Quot.sound。
-/

-- 迭代、接受与最小性
#check @APDAL.states
#check @APDAL.next_primal
#check @APDAL.next_dual
#check @APDAL.next_accept
#check @APDAL.next_minimal
#check @APDAL.accept_cond_of_K_zero
#check @APDAL.accept_cond_of_zero_dual

-- 标量增长、强凸支持与单步能量
#check @APDAL.scalar_growth
#check @APDAL.strong_prox_optimality
#check @APDAL.local_energy

-- 步长下界与二次增长
#check @APDAL.q_lower_all
#check @APDAL.weighted_theta_next
#check @APDAL.quadratic_growth

-- 能量连接、加权恒等式、平均点与联合界
#check @APDAL.state_energy
#check @APDAL.ergWeight_smul_sum
#check @APDAL.averaged_gap_le_sum
#check @APDAL.joint_bound_dom
#check @APDAL.joint_bound_arbitrary

-- 两条速率
#check @APDAL.main_rate

#print axioms APDAL.states
#print axioms APDAL.next_primal
#print axioms APDAL.next_dual
#print axioms APDAL.next_accept
#print axioms APDAL.next_minimal
#print axioms APDAL.accept_cond_of_K_zero
#print axioms APDAL.accept_cond_of_zero_dual
#print axioms APDAL.scalar_growth
#print axioms APDAL.strong_prox_optimality
#print axioms APDAL.local_energy
#print axioms APDAL.q_lower_all
#print axioms APDAL.weighted_theta_next
#print axioms APDAL.quadratic_growth
#print axioms APDAL.state_energy
#print axioms APDAL.ergWeight_smul_sum
#print axioms APDAL.averaged_gap_le_sum
#print axioms APDAL.joint_bound_dom
#print axioms APDAL.joint_bound_arbitrary
#print axioms APDAL.main_rate
