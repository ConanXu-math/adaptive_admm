# PDAL 核查记录

PDAL 使用本仓库已有 Optlib 与 mathlib，Lean 版本固定为 `v4.24.0-rc1`。
主要声明和条件范围见 [数学说明](../pdal.md)。

在仓库根目录执行：

```bash
lake build PDAL PDAL.AxiomCheck PDAL.PrintAxioms
lake env lean PDAL/PrintAxioms.lean
lake env lean --deps PDAL/PrintAxioms.lean
```

两条主要核查命令均退出0，独立构建完成7233 jobs。
构建完整输出为 [build.log](build.log)，完整类型与公理输出为
[axioms.log](axioms.log)，真实退出码分别为
[build.exit_code.txt](build.exit_code.txt) 和 [axioms.exit_code.txt](axioms.exit_code.txt)。
`--deps` 用于确认本仓库新生成的 `PDAL/Definitions.olean`。

新增默认目标后的全仓库 `lake build` 也退出0，完成7267 jobs，完整输出与退出码为
[default-build.log](default-build.log) 和
[default-build.exit_code.txt](default-build.exit_code.txt)。

核查文件 `PDAL/PrintAxioms.lean` 覆盖19项公理依赖：

`pdal_main`、`pdal_main_rate`、`pdal_main_ergodic`、`pdal_bounded`、
`pdal_cluster_point_saddle`、`pdal_has_saddle_cluster_point`、`pdal_convergence`、
`pdal_ergodic_dom`、`pdal_ergodic_rate`、`pdal_ergodic_rate_O1`、`mkPDAL_spec`、
`prox_scale_exists`、`prox_scale_unique`、`prox_scale_optimality`、
`linesearch_terminates`、`min_accept_index`、`tau_lower_bound`、
`theta_upper_bound`、`energy_inequality`。

全部19项依赖均为 `[propext, Classical.choice, Quot.sound]`。

交付源码的 SHA256 清单为 `sources.sha256`。主证明正文与原始 GLM 成果保持一致；
分离辅助仅补充文件末尾换行。完整原生会话与历史检查保留于研究档案。
