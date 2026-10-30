# AdGD 的 Lean 形式化

本项目形式化了 Malitsky–Mishchenko 的 *Adaptive Gradient Descent without Descent*，覆盖 Algorithm 1 的序列约束与具体步长规则、Lemma 1，以及 Theorem 1 的有界性、带权平均点的 $O(1/k)$ 速率和整列收敛。

证明入口为 [`AdGD.lean`](../AdGD.lean)，全部定义与证明位于 [`AdGD/Definitions.lean`](../AdGD/Definitions.lean)。模块直接使用本仓库的 Optlib 和 mathlib。

## 数学条件与算法

设 $E$ 为有限维完备实内积空间，$f:E\to\mathbb R$ 为凸函数，$g:E\to E$ 满足对所有 $x$ 都有 `HasGradientAt f (g x) x`，并假设存在极小点 $x^\star$。

`GradientLocallyLipschitz g` 采用球上的表述：对任意中心 $a$ 和半径 $R\geq0$，存在 $L>0$，使球内任意两点满足

$$
\|g(x)-g(y)\|\leq L\|x-y\|.
$$

常数 $L$ 可以随球改变。证明先建立迭代点有界性，再为包含所有迭代点的球选择同一个 $L$。

`AdGD f g` 保存迭代序列、正步长、更新关系、梯度、凸性以及两项步长界。`MinStepsizeRule alg` 保存具体选择规则。主定理证明满足这些结构约束的序列具有所述性质。

更新关系为

$$
x_{k+1}=x_k-\lambda_k g(x_k),\qquad
\theta_k=\frac{\lambda_k}{\lambda_{k-1}}\quad(k\geq1).
$$

对 $k\geq2$，当梯度差非零时，

$$
\lambda_k=\min\left\{
\sqrt{1+\theta_{k-1}}\lambda_{k-1},\;
\frac{\|x_k-x_{k-1}\|}{2\|g(x_k)-g(x_{k-1})\|}
\right\}.
$$

梯度差为零时选取增长项。初始化单独处理：第一次梯度差非零时使用曲率比值，梯度差为零时允许任意正的 $\lambda_1$。`min_rule_implies_growth` 和 `min_rule_implies_curvature` 分别证明具体规则满足分析所需的增长界与曲率界。

## 已证结果

| 数学结论 | Lean 声明 | 内容 |
| --- | --- | --- |
| Lemma 1 | `energy_inequality` | 单步能量不等式 |
| 能量递减 | `energy_nonincreasing` | 对 $k\geq1$，$E_{k+1}\leq E_k$ |
| Theorem 1：有界性 | `bounded`、`all_iterates_bounded` | 包含 $x_0$ 的全部迭代点有界 |
| 步长下界 | `stepsize_lower_bound` | $\lambda_k\geq c=\min\{\lambda_1,1/(2L)\}>0$ |
| Theorem 1：速率 | `rate_theorem_from_local` | 存在同一个 $L>0$，对全部 $k\geq1$ 给出带权平均速率 |
| 梯度趋零 | `gradient_tendsto_zero` | $\|g(x_k)\|\to0$ |
| 聚点最优性 | `cluster_point_is_minimizer` | 每个聚点均为极小点 |
| 函数值收敛 | `function_values_tendsto_optimal` | $f(x_k)-f(x^\star)\to0$ |
| 能量极限 | `energy_limit_exists` | 对任意极小点，能量序列存在极限 |
| 聚点唯一性 | `unique_cluster_point` | 任意两个极小点聚点相等 |
| Theorem 1：整列收敛 | `full_convergence` | 存在极小点 $\bar x$，使 $x_k\to\bar x$ |

能量定义为

$$
E_k(x^\star)=\|x_k-x^\star\|^2
+\frac12\|x_k-x_{k-1}\|^2
+2\lambda_k\theta_k\bigl(f(x_{k-1})-f(x^\star)\bigr).
$$

记 $D=E_1(x^\star)$，$S_k=\sum_{i=1}^{k}\lambda_i+\lambda_1\theta_1$。通过非负权重求和与 Jensen 不等式，源码中 `weighted_average` 定义的带权平均点满足

$$
f(\widehat x_k)-f(x^\star)
\leq\frac{D}{2S_k}
\leq\frac{D}{2kc},\qquad k\geq1.
$$

整列收敛采用 Opial 型论证。加强能量估计给出梯度趋零，梯度连续性与凸性给出聚点最优性。极小点之间的能量差等于对应距离平方之差，沿收敛子列取极限得到 `cluster_point_energy_identity`。由对称关系证明聚点唯一，再利用有限维空间的紧性得到整列收敛。

## 构建与导入

本仓库的 Lean 和 mathlib 均使用 `v4.24.0-rc1`。安装 elan 后，在仓库根目录执行：

```bash
lake exe cache get
lake build AdGD
```

`lake build` 同时包含 Adaptive ADMM 和 AdGD 的默认构建目标。其他 Lean 文件可以导入：

```lean
import AdGD
```

对主要声明执行公理检查：

```bash
printf '%s\n' \
  'import AdGD' \
  '#print axioms energy_inequality' \
  '#print axioms improved_energy_inequality' \
  '#print axioms all_iterates_bounded' \
  '#print axioms rate_theorem_from_local' \
  '#print axioms full_convergence' \
  | lake env lean --stdin
```

主要定理仅依赖 `[propext, Classical.choice, Quot.sound]`。AdGD 源码没有 `sorry`、`admit` 或新增未证公理。

## 来源

Yura Malitsky 与 Konstantin Mishchenko，*Adaptive Gradient Descent without Descent*，ICML 2020，Algorithm 1、Lemma 1、Theorem 1。

[论文与正式发表信息](https://proceedings.mlr.press/v119/malitsky20a.html) · [论文全文](https://proceedings.mlr.press/v119/malitsky20a/malitsky20a.pdf)
