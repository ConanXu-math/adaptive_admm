# 自适应ADMM框架设计文档

## 概述

本框架旨在支持：
1. **C1和C2条件的完整形式化**：分别处理参数增长和减小的情况
2. **Strategy1收敛性证明**：验证特定自适应策略的收敛性
3. **LLM代码生成接口**：允许LLM搜索论文并自动生成符合框架的Lean4代码

## 文件结构

```
AdaptiveADMM/
├── 核心文件（共享）
│   ├── AdaptiveScheme.lean              # ADMM基础定义
│   ├── AdaptiveLemmas.lean              # 共享引理和定义
│   │   ├── Setting类                    # 基础设置
│   │   ├── g1函数                       # C1条件的Lyapunov函数
│   │   ├── g2函数                       # C2条件的Lyapunov函数
│   │   ├── T_HWY, e₁, e₂, ey等辅助定义
│   │   └── 基础引理
│   └── AdaptiveInv_bounded.lean        # 有界性引理
│
├── C1条件相关
│   ├── AdaptiveCondition1.lean          # C1条件定义和相关引理
│   └── AdaptiveTheorem_converge_c1.lean # C1收敛定理
│
├── C2条件相关
│   ├── AdaptiveCondition2.lean          # C2条件定义和相关引理
│   └── AdaptiveTheorem_converge_c2.lean # C2收敛定理（待实现）
│
├── Strategies/
│   ├── Strategy1_Convergence.lean      # Strategy1收敛性证明
│   ├── Strategy2_Convergence.lean      # Strategy2收敛性证明（未来）
│   └── Strategy_Template.lean          # 策略模板（供LLM使用）
│
├── LLM_Interface/
│   ├── LLM_CodeGeneration.lean         # LLM代码生成接口
│   ├── Condition_Checker.lean          # 条件检查器
│   └── Strategy_Validator.lean         # 策略验证器（待实现）
│
├── ParameterAdaptation.lean            # 参数自适应策略定义
├── HWY_FORMALIZATION_GUIDE.md          # HWY论文形式化指南
├── FRAMEWORK_DESIGN.md                 # 本文件
├── FRAMEWORK_SUMMARY.md                # 框架总结
└── README.md                           # 使用指南
```

## 核心组件说明

### 1. 共享定义（AdaptiveLemmas.lean）

这是整个框架的核心文件，包含所有共享的定义和引理：

#### 关键定义

- **Setting类**: 基础设置，包含所有notation和共享变量
- **g1函数**: C1条件的Lyapunov函数
  ```lean
  g1 n = ‖ey n‖² + τ * ρₙ n² * ‖A₂ (e₂ n)‖² 
         + τ * (T_HWY - τ) * ρₙ n² * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖²
  ```
- **g2函数**: C2条件的Lyapunov函数
  ```lean
  g2 n = 1 / ρₙ n² * ‖ey n‖² + τ * ‖A₂ (e₂ n)‖² 
         + τ * (T_HWY - τ) * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖²
  ```
- **辅助变量**: `T_HWY`, `e₁`, `e₂`, `ey`, `u`, `v`等
- **基础引理**: `u_inthesubgradient`, `v_inthesubgradient`等

#### 设计原则

- 所有共享定义集中在一个文件中，便于维护
- C1和C2条件文件都导入 `AdaptiveLemmas.lean` 来访问共享定义
- 避免重复定义，确保一致性

### 2. C1和C2条件

#### C1条件（参数增长情况）

**文件**: `AdaptiveCondition1.lean`

**核心组件**:
- `Condition_C1` 类：定义C1收敛条件
- `η_k` 序列：控制参数增长速率
- `h1` 函数：基于g1的递推关系
  ```lean
  h1 n = -g1(n+1) + (1 + (η_k n)²) * g1 n
  ```

**条件要求**:
- `Σ ηₖ² < ∞` (η平方和有限)
- `∏(1 + ηₖ²) < ∞` (乘积有界)

**适用场景**: 当 `ρₙ(n+1) ≥ ρₙ(n)` 时

#### C2条件（参数减小情况）

**文件**: `AdaptiveCondition2.lean`

**核心组件**:
- `Condition_C2` 类：定义C2收敛条件
- `θ_k` 序列：控制参数减小速率
- `h2` 函数：基于g2的递推关系（待实现）
  ```lean
  h2 n = -g2(n+1) + (1 + (θ_k n)²) * g2 n
  ```

**条件要求**:
- `Σ θₖ² < ∞` (θ平方和有限)
- `∏(1 + θₖ²) < ∞` (乘积有界)

**适用场景**: 当 `ρₙ(n+1) ≤ ρₙ(n)` 时

### 3. g1 和 g2 的设计原理

#### g1的设计（参数增长情况）

当参数 `ρₙ` 增长时：
- 各项的系数都包含 `ρₙ²`，使得当 `ρₙ` 增大时，各项的权重相应增大
- 这反映了参数增长时对收敛性的影响
- 通过 `η_k` 控制增长速率，确保收敛

#### g2的设计（参数减小情况）

当参数 `ρₙ` 减小时：
- 第一项系数为 `1/ρₙ²`，当 `ρₙ` 减小时，该项权重增大，补偿参数减小的影响
- 后两项不依赖 `ρₙ`，保持稳定
- 通过 `θ_k` 控制减小速率，确保收敛

### 4. Strategy1收敛性证明

**文件**: `Strategies/Strategy1_Convergence.lean`

**目标**: 证明Strategy1满足C1条件，从而保证收敛性

**结构**:
```lean
-- Strategy1的定义
class Strategy1 where
  -- Strategy1的参数更新规则
  ρ_update : ℕ → ℝ → ℝ
  -- Strategy1满足单调递增
  h_strategy_monotone : ∀ k, admm.ρₙ (k+1) ≥ admm.ρₙ k
  
-- Strategy1满足C1条件
instance strategy1_satisfies_C1 : Condition_C1 ... where
  -- 定义η_k并证明条件
  -- 使用g1进行证明
  
-- Strategy1收敛性定理
theorem strategy1_converges [Strategy1] [Condition_C1 ...] : ...
```

### 5. LLM代码生成接口

**文件**: `LLM_Interface/LLM_CodeGeneration.lean`

**目的**: 提供标准化的接口，让LLM可以：
1. 搜索论文中的自适应策略
2. 识别策略的形式（C1或C2）
3. 自动选择正确的Lyapunov函数（g1或g2）
4. 生成符合框架的Lean4代码
5. 验证生成的代码满足收敛条件

**接口设计**:
```lean
-- 策略描述结构
structure StrategyDescription where
  name : String
  condition_type : ConditionType  -- C1 或 C2
  update_rule : String           -- 更新规则的数学描述
  paper_reference : String        -- 论文引用
  
-- 自动选择Lyapunov函数
def select_lyapunov_function (desc : StrategyDescription) : String :=
  match desc.condition_type with
  | ConditionType.C1 => "g1"  -- 使用g1
  | ConditionType.C2 => "g2"  -- 使用g2
  | ConditionType.Both => "both"  -- 需要同时使用g1和g2
```

## 使用流程

### 对于研究人员

1. **形式化新策略**:
   ```lean
   -- 1. 在Strategies/中创建新文件
   -- 2. 定义策略类
   class MyStrategy where
     -- 策略定义
   
   -- 3. 判断策略类型
   -- 如果参数可能增长 → 使用C1和g1
   -- 如果参数可能减小 → 使用C2和g2
   
   -- 4. 证明满足C1或C2
   instance : Condition_C1 MyStrategy where
     -- 使用g1进行证明
   
   -- 5. 应用收敛定理
   theorem my_strategy_converges [MyStrategy] [Condition_C1 ...] : ...
   ```

2. **验证现有策略**:
   - 使用 `Condition_Checker.lean` 中的工具
   - 检查策略是否满足收敛条件
   - 确认使用了正确的Lyapunov函数

### 对于LLM/AI Agent

1. **搜索论文**:
   - 识别自适应参数更新规则
   - 提取数学公式
   - 判断策略类型（增长型→C1，减小型→C2）

2. **生成代码**:
   ```lean
   -- 使用LLM_CodeGeneration接口
   let desc := StrategyDescription.mk 
     "Strategy from Paper X"
     ConditionType.C1  -- 或 ConditionType.C2
     "ρ_{k+1} = min(α * ρ_k, ρ_max)"
     "Paper X, 2023"
   
   -- 自动选择g1或g2
   let lyapunov := select_lyapunov_function desc
   let code := generate_strategy_code desc lyapunov
   ```

3. **验证收敛性**:
   ```lean
   -- 自动验证
   if verify_condition code desc.condition_type then
     -- 应用收敛定理
   else
     -- 报告错误
   ```

## 扩展性设计

### 添加新条件类型

如果未来需要C3、C4等条件：
1. 在 `AdaptiveLemmas.lean` 中定义新的Lyapunov函数（如 `g3`）
2. 创建对应的条件文件（如 `AdaptiveCondition3.lean`）
3. 在 `ConditionType` 中添加新类型
4. 更新验证器

### 添加新策略

1. 在 `Strategies/` 目录创建新文件
2. 遵循 `Strategy_Template.lean` 的模板
3. 根据策略特性选择C1（使用g1）或C2（使用g2）
4. 证明满足相应的收敛条件

### 修改Lyapunov函数

如果需要修改g1或g2的定义：
1. 在 `AdaptiveLemmas.lean` 中修改
2. 更新所有使用该函数的文件
3. 确保C1和C2的证明仍然成立

## 文件依赖关系图

```
AdaptiveScheme.lean
    │
    ├──→ 定义：ADMM, OptProblem, Convex_KKT
    │
    ↓
AdaptiveLemmas.lean
    │
    ├──→ 导入：AdaptiveScheme
    ├──→ 定义：Setting, g1, g2, T_HWY, e₁, e₂, ey, u, v
    ├──→ 引理：u_inthesubgradient, v_inthesubgradient等
    │
    ├──→ AdaptiveCondition1.lean
    │       │
    │       ├──→ 导入：AdaptiveLemmas
    │       ├──→ 定义：Condition_C1, η_k, h1
    │       ├──→ 使用：g1
    │       │
    │       └──→ AdaptiveTheorem_converge_c1.lean
    │               │
    │               ├──→ 导入：AdaptiveCondition1
    │               └──→ 使用：g1, h1, Condition_C1
    │
    └──→ AdaptiveCondition2.lean
            │
            ├──→ 导入：AdaptiveLemmas
            ├──→ 定义：Condition_C2, θ_k, h2（待实现）
            ├──→ 使用：g2
            │
            └──→ AdaptiveTheorem_converge_c2.lean（待实现）
                    │
                    ├──→ 导入：AdaptiveCondition2
                    └──→ 使用：g2, h2, Condition_C2
```

## 验证和测试

### 单元测试
- 每个条件类型应有独立的测试
- 每个策略应有收敛性验证
- 验证g1和g2的正确性

### 集成测试
- LLM生成的代码应通过验证器
- 所有策略应能正确应用收敛定理
- 确保C1策略使用g1，C2策略使用g2

## 设计决策说明

### 为什么分离g1和g2？

1. **数学原因**：参数增长和减小需要不同的Lyapunov函数形式
2. **清晰性**：明确区分两种不同的收敛情况
3. **可维护性**：每个函数有明确的用途，便于理解和修改

### 为什么共享定义在AdaptiveLemmas.lean？

1. **避免重复**：g1和g2共享很多辅助定义（e₁, e₂, ey等）
2. **一致性**：确保所有文件使用相同的定义
3. **依赖管理**：清晰的依赖关系，便于维护

### 为什么C1和C2条件分开文件？

1. **模块化**：每个条件独立，便于开发和测试
2. **清晰性**：明确区分两种不同的收敛条件
3. **可扩展性**：未来可以轻松添加C3、C4等条件

## 参考文献

1. He, B. S., Yang, H., & Wang, S. L. (2000). Alternating direction method with self-adaptive penalty parameters for monotone variational inequalities. *Journal of Optimization Theory and Applications*, 106(2), 337-356.

2. 其他相关自适应ADMM论文

## 维护和更新

- **版本控制**: 使用Git跟踪所有更改
- **文档更新**: 每次添加新功能时更新本文档
- **代码审查**: 所有LLM生成的代码需要人工审查
- **依赖管理**: 确保导入关系正确，避免循环依赖

## 未来计划

1. **完成C2条件**：
   - 实现h2函数
   - 完成C2相关的收敛引理
   - 实现C2收敛定理

2. **完善Strategy1**：
   - 完成所有证明细节
   - 验证收敛性

3. **扩展LLM接口**：
   - 实现Strategy_Validator
   - 增强代码生成能力
   - 自动选择g1或g2
