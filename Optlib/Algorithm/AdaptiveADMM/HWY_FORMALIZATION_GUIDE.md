# HWY论文形式化指南

## 概述

本指南说明如何将opt2论文中的固定参数ADMM证明转换为HWY论文中的自适应参数ADMM证明。

## HWY vs opt2 对照表

| 特性                   | opt2 (固定ρ)                               | HWY (自适应ρₙ)                                        |
| ---------------------- | ------------------------------------------- | ------------------------------------------------------- |
| **Lyapunov函数** | Ψ(n) = 1/(τρ)‖ey‖² + ρ‖A₂e₂‖²   | Ψ_HWY(n) = 1/(τρₙ(n))‖ey‖² + ρₙ(n)‖A₂e₂‖² |
| **扩展函数**     | Φ(n) = Ψ(n) + (1-τ)ρ‖A₁e₁+A₂e₂‖² | 类似但系数随n变化                                       |
| **交叉项M**      | M(n) = (1-τ)ρ⟨A₂(x₂ⁿ-x₂ⁿ⁻¹), r⟩  | M(n) = (1-τ)ρₙ(n-1)⟨A₂(x₂ⁿ-x₂ⁿ⁻¹), r⟩       |
| **收敛条件**     | 无（ρ固定）                                | Condition C1/C2（控制ρ变化速度）                       |

## 核心定理对应关系

### HWY Lemma 3.1

- **对应位置**: HWY原文第374-423行
- **对应引理**: 在 `AdaptiveLemmas.lean`中已有类似的 `u_inthesubgradient`和 `v_inthesubgradient`
- **核心思想**: 利用凸函数的subgradient单调性

### HWY Lemma 3.2

- **对应位置**: HWY原文第455-488行，公式(28)
- **对应引理**: `Φ_isdescending_inequ3`（已证明）
- **结论**: `ρₙ(n+1) ⟨r_{n+1}, A₂Δx₂⟩ ≤ (1-τ)ρₙ(n) ⟨rₙ, A₂Δx₂⟩`

### HWY Theorem 3.1

- **对应位置**: HWY原文第504-562行，公式(33)
- **对应引理**: 扩展 `Φ_isdescending_inequ5`，需要处理ρₙ变化
- **核心**: 证明Ψ_HWY递降（模ρ变化误差项）

## 已完成的工作

### 1. 基础设施

- ✅ 定义 `Ψ_HWY`: adaptive Lyapunov函数
- ✅ 定义 `η_k`和 `θ_k`: 参数变化的控制序列
- ✅ 定义 `Condition_C1`和 `Condition_C2`: 收敛条件

### 2. 核心引理框架

- ✅ `HWY_Lemma_3_1`: 框架已建立（需要填充证明）
- ✅ `HWY_Lemma_3_2`: 框架已建立，指出与 `Φ_isdescending_inequ3`的关系
- ✅ `HWY_Theorem_3_1`: 主定理框架
- ✅ `HWY_Convergence`: 收敛定理框架

### 3. 辅助引理

- ✅ `rho_change_term`: 处理ρ变化对A₂e₂项的影响
- ✅ `ey_change_with_rho`: 处理ρ变化对ey项的影响
- ✅ `HWY_cross_term_estimate`: Cauchy-Schwarz不等式框架
- ✅ `T_HWY`和 `T_minus_tau_positive`: HWY论文的T参数

## 下一步工作

### 阶段1: 完成核心引理（优先级：高）

1. **HWY_Lemma_3_1的证明**

   ```lean
   -- 利用已有的：
   - u_inthesubgradient (n+1)
   - v_inthesubgradient (n+1)  
   - subgradientAt_mono_u (n+1)
   - subgradientAt_mono_v (n+1)
   - admm_kkt.h.eq (KKT条件)

   -- 推导步骤：
   (1) 从subgradient单调性：⟨u(n+1) + A₁†y', e₁(n+1)⟩ ≥ 0
   (2) 展开u(n+1)的定义
   (3) 使用adjoint性质：⟨A₁†z, x⟩ = ⟨z, A₁x⟩
   (4) 整理得到所需不等式
   ```
2. **HWY_cross_term_estimate的证明**

   ```lean
   -- 标准Cauchy-Schwarz不等式：
   2|⟨a, b⟩| ≤ α‖a‖² + (1/α)‖b‖²

   -- 选择α = (τρₙ(n)²) / ((1-τ)ρₙ(n+1)²)
   ```
3. **T_minus_tau_positive的证明**

   ```lean
   -- 代数计算：
   T - τ = (1/2)(τ² - 3τ + 3)
        = (1/2)((τ - 3/2)² + 3/4)
        ≥ 3/8
   ```

### 阶段2: 完成主定理（优先级：高）

**HWY_Theorem_3_1的证明**

```lean
证明大纲：
(1) 展开Ψ_HWY(n+1) - Ψ_HWY(n)
(2) 使用ey_change_with_rho和rho_change_term分解
(3) 应用HWY_Lemma_3_1和HWY_Lemma_3_2
(4) 使用HWY_cross_term_estimate处理交叉项
(5) 利用M_le控制2M(n+1)项
(6) 整理得到最终递降不等式
```

### 阶段3: 桥接到已有证明（优先级：中）

1. **opt2_to_HWY_bridge的证明**

   - 说明 `Φ_isdescending_inequ5`如何推导HWY的不等式
   - 关键：当ρₙ固定时，两个证明体系重合
2. **from_opt2_Phi_to_HWY的证明**

   - 组合各个ρ变化项
   - 证明opt2的Φ可以推广到HWY的Ψ_HWY

### 阶段4: 收敛性证明（优先级：中）

1. **HWY_Convergence的证明**（在Condition_C1下）

   ```lean
   证明步骤：
   (1) 从HWY_Theorem_3_1累加：Σ[递降项] < ∞
   (2) 利用η²可和：Σ(1+η²) = ∏(1+η²) < ∞
   (3) Telescope sum: Ψ_HWY(N) ≤ Ψ_HWY(1)∏(1+η²)
   (4) 因此Ψ_HWY有界
   (5) 从递降项的可和性推出极限为0
   ```
2. **Condition_C2下的收敛性**

   - 类似证明，使用θ_k而非η_k

### 阶段5: Strategy验证（优先级：低）

证明HWY论文第2节中的三个策略满足Condition C1/C2：

- Strategy S1（单调增）→ Condition C1
- Strategy S2（单调减）→ Condition C2
- Strategy S3（自适应）→ 同时满足C1和C2

## 可重用的已有引理

以下opt2中的引理可以直接用于HWY证明：

| opt2引理                                       | 用途                    |
| ---------------------------------------------- | ----------------------- |
| `u_inthesubgradient`                         | HWY_Lemma_3_1的一部分   |
| `v_inthesubgradient`                         | HWY_Lemma_3_1的另一部分 |
| `subgradientAt_mono_u`                       | 单调性                  |
| `subgradientAt_mono_v`                       | 单调性                  |
| `Φ_isdescending_inequ3`                     | 就是HWY_Lemma_3_2！     |
| `M_le`                                       | 控制M项的界             |
| `basic_inequ₁'`, `basic_inequ₂`          | 基本不等式              |
| `expended_u_gt_zero`, `expended_v_gt_zero` | 展开后非负性            |

## 技术难点

### 1. ρ变化项的处理

- **问题**: 当ρₙ(n+1) ≠ ρₙ(n)时，会产生额外的误差项
- **解决**: 用Condition C1/C2控制参数变化速度，使误差项可和

### 2. Telescope Sum技巧

- **HWY公式(51)-(52)**：利用
  ```
  Ψ(n+1) ≤ (1+η²ₙ)Ψ(n) - [正项]
  ```
- 累乘得到：
  ```
  Ψ(N) ≤ Ψ(1)∏(1+η²ᵢ) - Σ[正项]
  ```

### 3. 与ParameterAdaptation.lean的集成

- 需要证明 `AdaptiveStrategies`中定义的策略满足Condition C1/C2
- 连接到 `AdaptiveConvergence.lean`中的收敛定理

## 预期时间

- 阶段1-2: 核心引理和主定理（3-5天）
- 阶段3: 桥接证明（1-2天）
- 阶段4: 收敛性证明（2-3天）
- 阶段5: Strategy验证（1-2天）

**总计**: 约7-12天完成整个形式化证明

## 参考文献

1. He, B. S., Yang, H., & Wang, S. L. (2000). Alternating direction method with self-adaptive penalty parameters for monotone variational inequalities. *Journal of Optimization Theory and Applications*, 106(2), 337-356.
2. opt2论文中的ADMM收敛性证明

## 文件结构

```
AdaptiveADMM/
├── AdaptiveScheme.lean          # 自适应ADMM的定义
├── AdaptiveLemmas.lean          # 本文件：引理和定理
├── ParameterAdaptation.lean     # 参数自适应策略
├── AdaptiveConvergence.lean     # 收敛性定理汇总
└── HWY_FORMALIZATION_GUIDE.md   # 本指南
```
