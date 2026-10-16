# Adaptive ADMM 的 Lean 形式化

[English](README.en.md)

本项目使用 Lean 4 形式化证明变罚参数两块 ADMM 的收敛性，包含 C1、C2 两条收敛证明，以及可复用的增大、减小、保持罚参数的策略接口。

## 构建与使用

Lean 和 mathlib 均固定为 `v4.24.0-rc1`。安装 elan 后，在本目录运行：

```bash
lake exe cache get
lake build
```

默认构建包含 Adaptive ADMM 的统一入口、全部相关证明模块及其数学依赖。使用时导入：

```lean
import Optlib.Algorithm.AdaptiveADMM

#check KKTPoint
#check AdaptiveADMM_Convergence_Proof.adaptive_admm_convergence_c1
#check AdaptiveADMM_Convergence_Proof.adaptive_admm_convergence
#check Strategy3.converges_from_policy
```

没有后缀的 `adaptive_admm_convergence` 是 C2 定理。原有的单模块导入路径仍可使用。`Optlib.lean` 属于更广泛的上游算法库，本项目使用上面的 Adaptive ADMM 入口。

检查自己的证明文件：

```bash
lake env lean -E hasSorry -DautoImplicit=false -DrelaxedAutoImplicit=false MyProof.lean
```

## 证明的问题与条件

考虑有限维实内积空间中的凸优化问题：

```text
minimize    f₁(x₁) + f₂(x₂)
subject to  A₁ x₁ + A₂ x₂ = b
```

完整收敛定理使用以下条件：

- 两个目标函数下半连续、凸且处处取有限实数值，并存在 KKT 点。
- 每一步都精确求解两个 ADMM 子问题。
- `A₁`、`A₂` 都是单射；对矩阵而言，对应满列秩。
- 罚参数序列具有有限上界和严格正的下界。
- 乘子更新使用固定松弛参数 `0 < τ < (1 + sqrt 5) / 2`。
- 罚参数的相对变化满足 C1 或 C2 条件。

定理证明两个原变量序列和乘子序列收敛到同一个 KKT 点的对应分量。

`Strategy3.converges_from_policy` 根据非负、可求和的调节幅度，以及增大、减小、保持三类实际递推，建立 C1 并应用收敛定理。裁剪策略使用沿实际罚参数序列计算的有效调节幅度。具体候选仍需证明参数条件、递推对应关系和问题假设；这些结果不会自动证明任意 Python 浮点程序与 Lean 模型等价。

## 显式传入 KKT 参考点

`KKTPoint admm` 保存原变量、乘子及其满足 KKT 条件的证明。误差和能量函数直接接收参考点，例如：

```text
e₁ admm reference n
ey admm reference n
g1 admm reference n
```

`Condition_C1 admm`、`Condition_C2 admm` 只描述罚参数条件，不再携带参考点。策略收敛接口的调用形式为：

```lean
Strategy3.converges_from_policy
  (admm := admm) reference policy h_rho fullrank₁ fullrank₂
```

证明先用原始参考点建立有界性并选取子列，再把得到的 `limitKKT` 显式传给最终误差和能量估计。选定的子列保持不变，核心证明不依赖 `Setting` 自动选择参考点。

`Compatibility.lean` 为历史证明保留 `Existance_of_kkt` 和空的 `Setting` 参数。新证明使用 `KKTPoint` 和显式参数；当前三个策略模板也采用这一接口。

## 源码结构

下列路径相对于 `Optlib/Algorithm/AdaptiveADMM/`：

| 模块 | 内容 |
| --- | --- |
| `AdaptiveScheme.lean` | 优化问题、迭代格式、KKT 条件和 `KKTPoint` |
| `AdaptiveDefinitions.lean` | 显式接收参考点的误差、能量及辅助序列 |
| `AdaptiveOptimality.lean` | 子问题凸性、求导和次梯度最优性 |
| `AdaptiveEnergyIdentities.lean` | 残差恒等式和次梯度单调性估计 |
| `AdaptiveEnergyDescent.lean` | 交叉项估计与公共能量下降不等式 |
| `AdaptiveLemmas.lean` | 公共最优性和下降结果的导入入口 |
| `AdaptiveCondition1.lean`、`AdaptiveCondition2.lean` | 罚参数变化、能量有界性和残差趋零 |
| `BoundednessC1.lean`、`BoundednessC2.lean` | 乘积归一化、迭代有界性和子列选取 |
| `ClusterPointC1.lean`、`ClusterPointC2.lean` | 子列极限与 KKT 聚点的构造 |
| `AdaptiveTheorem_converge_c1.lean`、`AdaptiveTheorem_converge_c2.lean` | 以聚点为参考的能量估计和整列收敛 |
| `SequenceConvergence.lean` | 从趋零子列推出整列趋零的公共标量引理 |
| `AdaptiveProductBounds.lean`、`AdaptiveInv_bounded.lean` | 乘积估计和单射线性映射的逆向界 |
| `Strategies.lean`、`Strategies/` | 策略接口、可求和调节序列、裁剪及 C1 连接 |

`Optlib/Convex`、`Optlib/Differential`、`Optlib/Function` 和 `Optlib/Optimality` 提供所需的基础数学结果。策略接口的详细说明见[策略指南](Optlib/Algorithm/AdaptiveADMM/Strategies/README.md)。

## 许可证

沿用上游的 [Apache 2.0 许可证](LICENSE.txt)，并保留源码作者说明。
