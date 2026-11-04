# Malitsky–Pock PDAL 的 Lean 4 形式化

本项目完成论文第1–2节的 Algorithm 1、Lemma 1 和 Theorem 1–2。
证明入口为 [PDAL.lean](../PDAL.lean)，主证明位于
[PDAL/Definitions.lean](../PDAL/Definitions.lean)。
完整主定理类型与19项公理依赖由 [PrintAxioms.lean](../PDAL/PrintAxioms.lean)
打印，核查输出见 [公理日志](pdal-verification/axioms.log)。

## 数学模型与条件

采用任意有限维实内积空间 $X,Y$、有界线性算子 $K$ 和一般 proper l.s.c.
扩展实值凸函数 $g,h$，假设存在鞍点。$h$ 对应原文的 $f^*$。
`ProperConvex` 使用显式定义域与域上实值函数，域外按 $+\infty$ 解释，
因此覆盖约束指示函数。定义域不要求闭，闭次水平集给出下半连续性；仿射下界由
原始非空、凸性和下半连续条件推导。

初始化保持任意 $x_0\in X$、$y_1\in Y$、$\tau_0>0$、
$0<\mu,\delta<1$、$\beta>0$、$\theta_0=1$。
对任意合法试探选择器，试探步长属于
$[\tau_{k-1},\tau_{k-1}\sqrt{1+\theta_{k-1}}]$。
每个候选重新计算外推和对偶近端点，取最小非负接受索引，并递归构造全部序列。
算子范数仅用于分析。线搜索证明覆盖 $K=0$ 和对偶增量为零。

## 已完成结论

| 目标 | 主要声明 |
|---|---|
| 近端点存在、唯一与最优性 | `prox_scale_exists`、`prox_scale_unique`、`prox_scale_optimality` |
| 线搜索有限终止、最小接受索引 | `linesearch_terminates`、`min_accept_index` |
| 原始数据的递归更新与接受条件 | `pdNext`、`pdSeq`、`mkPDAL`、`mkPDAL_spec` |
| 步长、外推参数和能量 | `tau_lower_bound`、`theta_upper_bound`、`energy_inequality` |
| 有界、全部聚点为鞍点及聚点存在 | `pdal_bounded`、`pdal_cluster_point_saddle`、`pdal_has_saddle_cluster_point` |
| 原题附加条件下整列收敛 | `pdal_convergence` |
| 原遍历间隙界、平均点域与 $O(1/N)$ | `pdal_ergodic_dom`、`pdal_ergodic_rate`、`pdal_ergodic_rate_O1` |

三个最终主定理均直接接收原始数据与合法选择器，并对同一 `mkPDAL` 序列给出：

- `pdal_main`：有界性、全部聚点为鞍点、聚点存在，以及条件整列收敛。
- `pdal_main_ergodic`：平均点属于相应定义域、间隙非负，以及有限常数界。
- `pdal_main_rate`：存在与 $N$ 无关的 $C\geq0$，使间隙至多为 $C/N$。

$x_0\in\operatorname{dom}g$ 仅用于有限常数速率。
域结论与间隙非负适用于任意初始化。
$g$ 在定义域上连续和步长上界仅用于整列收敛。

## 原平均与间隙常数

保留

$$
s_N=\sum_{k=1}^{N}\tau_k,\qquad
X_N=\frac{\tau_1\theta_1x_0+\sum_{k=1}^{N}\tau_k\bar x_k}
{\tau_1\theta_1+s_N},\qquad
Y_N=\frac{\sum_{k=1}^{N}\tau_k y_{k+1}}{s_N}.
$$

按原文定义 $P,D,G=P+D$。若 $x_0\in\operatorname{dom}g$，则

$$
0\leq G(X_N,Y_N)\leq
\frac{\|x_1-x^*\|^2/2+\|y_1-y^*\|^2/(2\beta)
+\tau_1\theta_1P(x_0)}{s_N}.
$$

$X_N$ 可表示为 $x_1,\ldots,x_N$ 的非负权组合，证明不要求外推点
$\bar x_k$ 位于定义域。步长正下界给出 $s_N\geq N\tau_{\min}$，进而得到
$O(1/N)$。

任务指定对偶平均使用 $y_{k+1}$，与式(20)及式(25)之后求和中的
$D(y_{k+1})$ 一致；原文 Theorem 2 与式(29)的印刷索引另行保留。
这一索引约定属于原始任务提供的外部帮助。

## 构建与独立核查

沿用本仓库的 Lean、mathlib `v4.24.0-rc1` 和已有 Optlib。在仓库根目录执行：

```bash
lake build PDAL PDAL.AxiomCheck PDAL.PrintAxioms
lake env lean PDAL/PrintAxioms.lean
```

核查命令、完整输出与退出码保存在 [pdal-verification](pdal-verification/README.md)。
数学正文沿用已验证的 GLM 成果；本仓库重新构建后再核对完整类型和公理依赖。
全部19项主要声明仅依赖 `propext`、`Classical.choice`、`Quot.sound`。
主证明原始 SHA256 为
`0c4b58cf5b6312474f52560d84dc45530f2b5f3d2a97ee9b8880edbafdf60279`。

## 来源与模型帮助

- 论文：Malitsky 与 Pock，
  [A first-order primal-dual algorithm with linesearch](https://arxiv.org/abs/1608.08883v2)，
  第1–2节。
- GLM 负责主证明正文的写入、修正与 Lean 检查。最终模型为
  `slai-glm/glm-5.3-flash`，variant `max`、reasoningEffort `max`。
- Codex 提供 CodexEnergyHelp、CodexBoundHelp、AffineSeparationHelp 辅助源码，
  以及多轮候选、数学诊断、接续和执行检查，并完成最终独立验证与仓库整理。
  CodexClusterHelp 源码来自此前 GLM。部分正确修改早于相应 Codex 提示，
  其 GLM 来源保持不变。
- 完整原生会话、提示、失败、中断、修改记录和真实退出码已原样存档至研究者的
  U 盘，并保留本机原件。未返回的内部推理及额外用量保持未知。
