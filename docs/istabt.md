# ISTA with backtracking 的 Lean 形式化

本项目形式化了 Beck–Teboulle 论文第 2–3 节的带回溯近端梯度法。证明包括近端点存在唯一性、接受索引存在性、最小索引、迭代序列构造、目标函数单调性，以及函数值误差的 $O(1/k)$ 界。

证明入口为 [ISTABt.lean](../ISTABt.lean)，主要定义与证明位于 [ISTABt/Definitions.lean](../ISTABt/Definitions.lean)，29 项公理检查位于 [ISTABt/AxiomCheck.lean](../ISTABt/AxiomCheck.lean)。

## 数学条件与近端模型

设 $E$ 为有限维完备实内积空间，目标函数为 $F=f+g$。假设：

- $f:E\to\mathbb R$ 凸，并存在梯度映射 $f'$，使每一点均满足 HasGradientAt。
- 存在 $L>0$，使 $\|f'(x)-f'(y)\|\leq L\|x-y\|$ 对所有 $x,y$ 成立。
- $g:E\to\mathbb R$ 连续且凸。
- $F$ 存在极小点。

对 $\ell>0$，定义

$$
Q_\ell(x,y)=f(y)+\langle x-y,f'(y)\rangle
+\frac{\ell}{2}\|x-y\|^2+g(x).
$$

**proxL** 定义 $p_\ell(y)$。它通过缩放函数 $g/\ell$ 的近端点构造，对应下列等价的极小化问题：

$$
p_\ell(y)=\operatorname*{argmin}_x
\left\{g(x)+\frac{\ell}{2}
\left\|x-\left(y-\ell^{-1}f'(y)\right)\right\|^2\right\}.
$$

**proxLExists**、**proxL_min**、**proxL_unique** 与 **proxL_subgrad** 分别给出存在性、最小化性质、唯一性及次梯度条件。

## 回溯与序列构造

给定任意初始点 $x_0$、初始参数 $L_0>0$ 和回溯因子 $\eta>1$。对 $k\geq1$，令 $i_k$ 为使下式成立的最小非负整数：

$$
F\!\left(p_{\eta^{i_k}L_{k-1}}(x_{k-1})\right)
\leq
Q_{\eta^{i_k}L_{k-1}}
\!\left(p_{\eta^{i_k}L_{k-1}}(x_{k-1}),x_{k-1}\right).
$$

随后取

$$
L_k=\eta^{i_k}L_{k-1},\qquad
x_k=p_{L_k}(x_{k-1}).
$$

接受条件由 **acceptAt** 表述，其参数包含当前点、当前正参数和 $\eta$。Lipschitz 常数用于证明接受索引存在：由 $\eta>1$，存在 $i$ 使 $\eta^i\ell\geq L$；**acceptance_when_large** 给出该候选满足接受条件。**acceptAt_exists** 完成这一存在性证明，**btIndex** 使用 Nat.find 选择最小索引，**btIndex_accept** 和 **btIndex_minimal** 证明接受性及最小性。

**StepState** 保存当前点、正参数及其正性证明、当前索引。**nextStep** 定义一次回溯更新，**stepStates** 从给定的 $x_0,L_0$ 递归构造全部状态。**xSeq**、**LkSeq** 和 **ikSeq** 是相应投影。

**seq_acceptance**、**seq_ik_minimal**、**seq_Lk_update** 和 **seq_x_update** 给出构造序列的全部动态性质。**mkISTABt** 使用这些证明构造 ISTABt，并保存给定的 $x_0,L_0,\eta$ 及问题参数。定义采用 Lean 的经典选择与 noncomputable 表述。

## 单调性与速率

设

$$
\overline L=\max\{L_0,\eta L\}.
$$

对任意极小点 $x^*$ 及 $k\geq1$，已证结论为

$$
0<L_k\leq\overline L,\qquad F(x_k)\leq F(x_{k-1}),
$$

以及

$$
F(x_k)-F(x^*)\leq
\frac{\overline L\|x_0-x^*\|^2}{2k}.
$$

该常数允许任意 $L_0>0$；当 $L_0\leq\eta L$ 时，$\overline L=\eta L$。

证明从论文 Lemma 2.3 的关键不等式得到

$$
F(x_k)-F(x^*)\leq
\frac{L_k}{2}
\left(\|x^*-x_{k-1}\|^2-\|x^*-x_k\|^2\right).
$$

极小点性质使左侧非负，因此距离平方之差非负。结合 $L_k\leq\overline L$ 可以采用同一系数 $\overline L/2$；再利用目标函数单调性和逐步累加，得到

$$
k\bigl(F(x_k)-F(x^*)\bigr)
\leq\frac{\overline L}{2}
\left(\|x^*-x_0\|^2-\|x^*-x_k\|^2\right)
\leq\frac{\overline L}{2}\|x^*-x_0\|^2.
$$

源码中的 **alg_rate** 以归纳法完成这一估计。最终定理 **istabt_rate** 对 **mkISTABt** 构造的序列应用该结果，参数直接来自原题数据与假设。

| 内容 | 主要声明 |
| --- | --- |
| 近端点性质 | proxLExists、proxL_min、proxL_unique、proxL_subgrad |
| 下降引理与接受条件 | descent_lemma、acceptance_when_large |
| 关键不等式 | key_inequality、key_inequality_min |
| 回溯终止与最小索引 | acceptAt_exists、btIndex、btIndex_accept、btIndex_minimal |
| 递归序列及其性质 | stepStates、seq_acceptance、seq_ik_minimal、seq_Lk_update、seq_x_update |
| 原始数据构造算法 | mkISTABt |
| 参数上界与单调性 | alg_Lk_le_bound、alg_Fx_monotone |
| 最终函数值速率 | istabt_rate |

## 构建与公理检查

本仓库使用 Lean 和 mathlib v4.24.0-rc1。在仓库根目录执行：

    lake build ISTABt ISTABt.AxiomCheck
    lake env lean ISTABt/AxiomCheck.lean

其他证明文件可导入：

    import ISTABt

AxiomCheck.lean 检查 29 项声明，公理依赖均为 propext、Classical.choice、Quot.sound。主要源码包含完整证明。

## 来源

Amir Beck 与 Marc Teboulle，A Fast Iterative Shrinkage-Thresholding Algorithm for Linear Inverse Problems，SIAM Journal on Imaging Sciences 2(1)，183–202，2009，第 2–3 节。

[正式发表页面](https://doi.org/10.1137/080716542) · [论文 PDF](https://www.ceremade.dauphine.fr/~carlier/FISTA)。
