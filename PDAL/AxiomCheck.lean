import PDAL.Definitions

/-! ### 完整类型核查 -/

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

/-! ### 公理依赖核查（只允许标准三公理）-/

#print axioms pdal_main
#print axioms pdal_main_rate
#print axioms pdal_main_ergodic
#print axioms pdal_convergence
#print axioms pdal_cluster_point_saddle
#print axioms pdal_ergodic_dom
#print axioms pdal_ergodic_rate
#print axioms pdal_ergodic_rate_O1
#print axioms mkPDAL_spec
