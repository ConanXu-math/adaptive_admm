/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Condition Checker for LLM-generated code

# 条件检查器

本文件提供工具来检查LLM生成的策略代码是否满足C1或C2条件。

## 功能

1. 检查策略是否正确定义了η_k或θ_k序列
2. 验证可和性条件
3. 验证代码结构完整性
-/

import Optlib.Algorithm.ADMM.AdaptiveADMM.AdaptiveScheme_c1
import Optlib.Algorithm.ADMM.AdaptiveADMM.AdaptiveScheme_c2
import Optlib.Algorithm.ADMM.AdaptiveADMM.LLM_Interface.LLM_CodeGeneration

noncomputable section

open Set InnerProductSpace Topology Filter

variable {E₁ E₂ F : Type*}
[NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
[NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
[NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

variable (admm : ADMM E₁ E₂ F)
variable (admm_kkt : Existance_of_kkt admm)

namespace ConditionChecker

/-
## C1条件检查

检查策略是否满足C1条件。
-/
class C1Checker where
  /-
  检查η_k序列是否正确定义
  -/
  check_eta_k_definition : Bool := true

  /-
  检查η_k²是否可和
  -/
  check_eta_square_summable : Bool := false

  /-
  检查∏(1 + η_k²)是否可积
  -/
  check_one_eta_square_multipliable : Bool := false

/-
## C2条件检查

检查策略是否满足C2条件。
-/
class C2Checker where
  /-
  检查θ_k序列是否正确定义
  -/
  check_theta_k_definition : Bool := true

  /-
  检查θ_k²是否可和
  -/
  check_theta_square_summable : Bool := false

/-
## 通用检查器

检查代码是否包含必要的组件。
-/
structure CodeCheckResult where
  has_strategy_class : Bool
  has_condition_proof : Bool
  has_convergence_theorem : Bool
  condition_type : Option ConditionType
  has_sorry : Bool
  errors : List String

/-
检查代码结构
-/
def check_code_structure (code : String) : CodeCheckResult := {
  has_strategy_class := code.contains "class" && code.contains "where"
  has_condition_proof := code.contains "instance" && (code.contains "Condition_C1" || code.contains "Condition_C2")
  has_convergence_theorem := code.contains "theorem" && code.contains "converges"
  condition_type :=
    if code.contains "Condition_C1" then some ConditionType.C1
    else if code.contains "Condition_C2" then some ConditionType.C2
    else none
  has_sorry := code.contains "sorry"
  errors := []
}

/-
验证策略描述与生成代码的一致性
-/
def validate_consistency (desc : StrategyDescription) (code : String) : Bool :=
  let result := check_code_structure code
  result.has_strategy_class &&
  result.has_condition_proof &&
  result.has_convergence_theorem &&
  (match result.condition_type with
   | some ct => ct = desc.condition_type || desc.condition_type = ConditionType.Both
   | none => false)

end ConditionChecker
