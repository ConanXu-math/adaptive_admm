# 自适应ADMM框架 基于optlib

## 概述

本框架提供了自适应ADMM算法的完整形式化，支持：
- **C1和C2条件的完整形式化**：分别处理参数增长和减小的情况
- **Strategy1收敛性证明**：验证特定自适应策略的收敛性
- **LLM代码生成接口**：允许LLM搜索论文并自动生成符合框架的Lean4代码

## 文件结构

```
AdaptiveADMM/
├── 核心文件（共享）
│   ├── AdaptiveScheme.lean              # ADMM基础定义（OptProblem, ADMM类等）
│   ├── AdaptiveLemmas.lean              # 共享引理和定义
│   │   ├── Setting类                    # 基础设置
│   │   ├── g1函数                       # C1条件的Lyapunov函数
│   │   ├── g2函数                       # C2条件的Lyapunov函数
│   │   ├── T_HWY, e₁, e₂, ey等辅助定义
│   │   └── 基础引理（u_inthesubgradient, v_inthesubgradient等）
│   └── AdaptiveInv_bounded.lean        # 有界性引理（共享）
│
├── C1条件相关
│   ├── AdaptiveCondition1.lean          # C1条件定义和相关引理
│   │   ├── Condition_C1类定义
│   │   ├── η_k序列定义
│   │   ├── h1函数（基于g1）
│   │   └── C1相关的收敛引理
│   └── AdaptiveTheorem_converge_c1.lean # C1收敛定理
│
├── C2条件相关
│   ├── AdaptiveCondition2.lean          # C2条件定义和相关引理
│   │   ├── Condition_C2类定义
│   │   ├── θ_k序列定义
│   │   ├── h2函数（基于g2，待实现）
│   │   └── C2相关的收敛引理
│   └── AdaptiveTheorem_converge_c2.lean # C2收敛定理（待实现）
│
├── Strategies/
│   ├── Strategy1_Convergence.lean      # Strategy1收敛性证明
│   └── Strategy_Template.lean          # 策略模板（供LLM使用）
│
├── LLM_Interface/
│   ├── LLM_CodeGeneration.lean         # LLM代码生成接口
│   └── Condition_Checker.lean          # 条件检查器
│
├── ParameterAdaptation.lean            # 参数自适应策略定义
├── HWY_FORMALIZATION_GUIDE.md          # HWY论文形式化指南
├── FRAMEWORK_DESIGN.md                 # 框架设计文档
├── FRAMEWORK_SUMMARY.md                # 框架总结
└── README.md                           # 本文件
```

## 核心概念

### g1 和 g2 函数

框架中定义了两个关键的Lyapunov函数，分别用于不同的收敛条件：

#### g1 - 用于C1条件（参数增长情况）

```lean
g1 n = ‖ey n‖² + τ * ρₙ n² * ‖A₂ (e₂ n)‖² 
       + τ * (T_HWY - τ) * ρₙ n² * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖²
```

**特点**：
- 系数中包含 `ρₙ n²`，适合参数增长的情况
- 当 `ρₙ` 增大时，各项的权重相应增大
- 用于证明参数增长时的收敛性

#### g2 - 用于C2条件（参数减小情况）

```lean
g2 n = 1 / ρₙ n² * ‖ey n‖² + τ * ‖A₂ (e₂ n)‖² 
       + τ * (T_HWY - τ) * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖²
```

**特点**：
- 第一项系数为 `1 / ρₙ n²`，当 `ρₙ` 减小时，该项权重增大
- 后两项不依赖 `ρₙ`，保持稳定
- 用于证明参数减小时的收敛性

### h1 和 h2 函数

- **h1**: 用于C1条件的递推关系
  ```lean
  h1 n = -g1(n+1) + (1 + (η_k n)²) * g1 n
  ```
  
- **h2**: 用于C2条件的递推关系（待实现）
  ```lean
  h2 n = -g2(n+1) + (1 + (θ_k n)²) * g2 n
  ```

### C1和C2条件

#### C1条件（参数增长情况）
- **文件**: `AdaptiveCondition1.lean`
- **控制序列**: `η_k` - 控制参数增长速率
- **定义**: 当 `ρₙ(n+1) > ρₙ(n)` 时，`η_k n = sqrt((ρₙ(n+1)/ρₙ(n))² - 1)`，否则为0
- **条件**: 
  - `Σ ηₖ² < ∞` (η平方和有限)
  - `∏(1 + ηₖ²) < ∞` (乘积有界)
- **Lyapunov函数**: 使用 `g1`
- **递推关系**: 使用 `h1`
- **适用场景**: 当 `ρₙ(n+1) ≥ ρₙ(n)` 时

#### C2条件（参数减小情况）
- **文件**: `AdaptiveCondition2.lean`
- **控制序列**: `θ_k` - 控制参数减小速率
- **定义**: 当 `ρₙ(n+1) < ρₙ(n)` 时，`θ_k n = sqrt(1 - (ρₙ(n)/ρₙ(n+1))²)`，否则为0
- **条件**: 
  - `Σ θₖ² < ∞` (θ平方和有限)
  - `∏(1 + θₖ²) < ∞` (乘积有界)
- **Lyapunov函数**: 使用 `g2`
- **递推关系**: 使用 `h2`（待实现）
- **适用场景**: 当 `ρₙ(n+1) ≤ ρₙ(n)` 时

## 快速开始

### 1. 理解文件组织

#### 共享定义（AdaptiveLemmas.lean）
- `Setting`: 基础设置类，包含所有共享的notation和定义
- `g1`, `g2`: 两个Lyapunov函数
- `T_HWY`, `e₁`, `e₂`, `ey`: 辅助变量
- `u`, `v`: subgradient相关的辅助函数
- 基础引理：`u_inthesubgradient`, `v_inthesubgradient`等

#### C1条件（AdaptiveCondition1.lean）
- `Condition_C1`: C1条件类
- `η_k`: 控制序列
- `h1`: 递推关系
- C1相关的收敛引理

#### C2条件（AdaptiveCondition2.lean）
- `Condition_C2`: C2条件类
- `θ_k`: 控制序列
- `h2`: 递推关系（待实现）
- C2相关的收敛引理（待完善）

### 2. 形式化新策略

使用 `Strategies/Strategy_Template.lean` 作为模板：

```lean
-- 1. 定义策略类
class YourStrategy where
  -- 策略参数和更新规则

-- 2. 判断策略类型（C1或C2）
-- 如果参数可能增长，使用C1和g1
-- 如果参数可能减小，使用C2和g2

-- 3. 证明满足C1或C2条件
instance your_strategy_satisfies_C1 : Condition_C1 ... where
  -- 定义η_k并证明条件
  -- 使用g1进行证明

-- 4. 应用收敛定理
theorem your_strategy_converges [Condition_C1 ...] : ...
```

### 3. 使用LLM生成代码

参考 `LLM_Interface/LLM_CodeGeneration.lean`：

```lean
-- 1. 创建策略描述
let desc := StrategyDescription.mk 
  "StrategyName"
  ConditionType.C1  -- 或 ConditionType.C2
  "ρ_{k+1} = ..."
  "Paper Reference"

-- 2. 生成代码（自动选择g1或g2）
let code := generate_complete_file desc

-- 3. 验证
if validate_consistency desc code then
  -- 代码有效
```

## 当前状态

### ✅ 已完成

- [x] ADMM基础定义 (`AdaptiveScheme.lean`)
- [x] 共享引理和定义 (`AdaptiveLemmas.lean`)
  - [x] `g1` 和 `g2` 的定义
  - [x] `Setting` 类
  - [x] 基础引理（u_inthesubgradient, v_inthesubgradient等）
- [x] C1条件的完整形式化 (`AdaptiveCondition1.lean`)
  - [x] `Condition_C1` 类定义
  - [x] `η_k` 序列定义
  - [x] `h1` 函数定义
  - [x] C1相关的收敛引理
- [x] C1收敛定理 (`AdaptiveTheorem_converge_c1.lean`)
- [x] C2条件的基础定义 (`AdaptiveCondition2.lean`)
  - [x] `Condition_C2` 类定义
  - [x] `θ_k` 序列定义
- [x] Strategy1收敛性证明框架
- [x] LLM代码生成接口
- [x] 策略模板
- [x] 框架设计文档

### 🚧 进行中

- [ ] C2条件的完整实现
  - [ ] `h2` 函数的实现
  - [ ] C2相关的收敛引理
  - [ ] C2收敛定理 (`AdaptiveTheorem_converge_c2.lean`)
- [ ] Strategy1的完整证明
- [ ] Strategy2的实现

### 📋 待实现

- [ ] C2相关的有界性引理
- [ ] `Strategy_Validator.lean`
- [ ] 更多策略的收敛性证明

## 使用指南

### 对于研究人员

1. **形式化新策略**：
   - 复制 `Strategy_Template.lean`
   - 填写策略定义
   - **关键**：确定使用 `g1`（C1，参数增长）还是 `g2`（C2，参数减小）
   - 证明满足相应的收敛条件
   - 应用收敛定理

2. **验证现有策略**：
   - 使用 `Condition_Checker.lean` 中的工具
   - 检查策略是否满足收敛条件
   - 确认使用了正确的Lyapunov函数（g1或g2）

### 对于LLM/AI Agent

1. **搜索论文**：
   - 识别自适应参数更新规则
   - 提取数学公式
   - **判断策略类型**：
     - 如果参数单调递增或可能增长 → 使用C1和g1
     - 如果参数单调递减或可能减小 → 使用C2和g2

2. **生成代码**：
   - 使用 `LLM_CodeGeneration.lean` 接口
   - 遵循 `Strategy_Template.lean` 模板
   - **根据策略类型自动选择**：
     - C1策略 → 使用 `g1` 和 `h1`
     - C2策略 → 使用 `g2` 和 `h2`

3. **验证收敛性**：
   - 使用 `Condition_Checker.lean` 验证
   - 确保满足C1或C2条件
   - 确保使用了正确的Lyapunov函数

## 关键定义说明

### η_k 和 θ_k

- **η_k**: C1条件的控制序列
  - 当 `ρₙ(n+1) > ρₙ(n)` 时：`η_k n = sqrt((ρₙ(n+1)/ρₙ(n))² - 1)`
  - 否则：`η_k n = 0`
  - 用于控制参数增长速率

- **θ_k**: C2条件的控制序列
  - 当 `ρₙ(n+1) < ρₙ(n)` 时：`θ_k n = sqrt(1 - (ρₙ(n)/ρₙ(n+1))²)`
  - 否则：`θ_k n = 0`
  - 用于控制参数减小速率

### 如何选择 g1 还是 g2？

**使用 g1 (C1条件)** 当：
- 策略中参数 `ρₙ` 可能增长
- 参数更新规则如：`ρ_{k+1} = min(α * ρ_k, ρ_max)` 其中 `α > 1`
- 参数单调递增

**使用 g2 (C2条件)** 当：
- 策略中参数 `ρₙ` 可能减小
- 参数更新规则如：`ρ_{k+1} = max(β * ρ_k, ρ_min)` 其中 `0 < β < 1`
- 参数单调递减

**同时满足C1和C2**：
- 如果策略可能增长也可能减小，需要同时满足两个条件

## 文件依赖关系

```
AdaptiveScheme.lean
    ↓
AdaptiveLemmas.lean (导入AdaptiveScheme)
    ↓
    ├──→ AdaptiveCondition1.lean (导入AdaptiveLemmas)
    │       ↓
    │   AdaptiveTheorem_converge_c1.lean (导入AdaptiveCondition1)
    │
    └──→ AdaptiveCondition2.lean (导入AdaptiveLemmas)
            ↓
        AdaptiveTheorem_converge_c2.lean (待实现)
```

## 参考文献

1. He, B. S., Yang, H., & Wang, S. L. (2000). Alternating direction method with self-adaptive penalty parameters for monotone variational inequalities. *Journal of Optimization Theory and Applications*, 106(2), 337-356.

2. 其他相关自适应ADMM论文

## 贡献指南

1. 新策略应遵循 `Strategy_Template.lean` 的结构
2. 所有证明应完整（避免使用 `sorry`）
3. 添加适当的文档和注释
4. 更新本README和相关文档
5. **重要**：根据策略类型正确使用 `g1` 或 `g2`
6. 确保导入关系正确（通过 `AdaptiveLemmas.lean` 访问共享定义）

## 联系方式

如有问题或建议，请参考 `FRAMEWORK_DESIGN.md` 和 `FRAMEWORK_SUMMARY.md` 获取更多详细信息。
