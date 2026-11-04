import PDAL.Definitions

/-! ## 完整类型核查（主要声明）-/

#check @mkPDAL
#check @mkPDAL_spec
#check @mkPDAL_x0
#check @mkPDAL_y0
#check @pdal_main
#check @pdal_main_rate
#check @pdal_main_ergodic
#check @pdal_bounded
#check @pdal_cluster_point_saddle
#check @pdal_has_saddle_cluster_point
#check @pdal_convergence
#check @pdal_ergodic_dom
#check @pdal_ergodic_rate
#check @pdal_ergodic_rate_O1
#check @tau_lower_bound
#check @theta_upper_bound
#check @energy_inequality
#check @linesearch_terminates
#check @min_accept_index
#check @prox_scale_exists
#check @prox_scale_unique
#check @prox_scale_optimality

/-! ## 公理依赖核查（原题主要声明；只允许标准三公理）-/

-- 最终主定理
#print axioms pdal_main
#print axioms pdal_main_rate
#print axioms pdal_main_ergodic
-- Theorem 1（有界、聚点、收敛）
#print axioms pdal_bounded
#print axioms pdal_cluster_point_saddle
#print axioms pdal_has_saddle_cluster_point
#print axioms pdal_convergence
-- Theorem 2（遍历定义域、有限常数率、O(1/N)）
#print axioms pdal_ergodic_dom
#print axioms pdal_ergodic_rate
#print axioms pdal_ergodic_rate_O1
-- Algorithm 1 递归构造
#print axioms mkPDAL_spec
-- 近端点：存在、唯一、最优性
#print axioms prox_scale_exists
#print axioms prox_scale_unique
#print axioms prox_scale_optimality
-- 线搜索与最小接受索引
#print axioms linesearch_terminates
#print axioms min_accept_index
-- Lemma 1：步长下界、外推上界、能量不等式
#print axioms tau_lower_bound
#print axioms theta_upper_bound
#print axioms energy_inequality
