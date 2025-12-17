# Lean4 形式化证明自适应 ADMM（工程化主线 + 关键代码片段）
> 对应工程的三层结构：**建模层 → 通用收敛层 → 策略实例层**，并在关键处附上 Lean4 代码片段（骨架级别）。
>

---

## 1. 工程分层：你在 Lean 里到底“证明了什么”
### 1.1 三层结构
1. **建模层（Problem + Algorithm + KKT）**  
把优化问题、ADMM 迭代序列、KKT 条件定义成 Lean 可引用的对象。  
文件：`AdaptiveScheme.lean`
2. **通用收敛层（C1/C2 假设下的总收敛定理）**  
用势函数（Lyapunov）+ 递推不等式推出：残差趋零、有界性、极限点满足 KKT、整列收敛。  
文件：`AdaptiveLemmas.lean`, `AdaptiveCondition1.lean`, `AdaptiveCondition2.lean`,  
`AdaptiveInv_bounded.lean`, `AdaptiveTheorem_converge_c1.lean`, `AdaptiveTheorem_converge_c2.lean`
3. **策略实例层（Strategy3 等）**  
对每个具体自适应罚参数更新规则，仅需证明它满足 `Condition_C1` 或 `Condition_C2`，然后 `apply` 总收敛定理。  
文件：`Strategy3_Convergence.lean`

> 总结：  
**通用收敛证明只写一次；每个策略只证明“我满足 C1/C2”即可复用收敛定理。**
>

---

## 2. 建模层：把“论文对象”翻译成 Lean 的 class / Prop
### 2.1 优化问题：`OptProblem`（数据 + 假设）
对应论文里：函数、约束、凸性、下半连续、最优解存在等。

```plain
class OptProblem (E₁ E₂ F : Type*) [NormedAddCommGroup E₁] [NormedAddCommGroup E₂] [NormedAddCommGroup F] := where
  f₁ : E₁ → ℝ
  f₂ : E₂ → ℝ
  A₁ : E₁ →L[ℝ] F
  A₂ : E₂ →L[ℝ] F
  b  : F
  lscf₁ : LowerSemicontinuous f₁
  lscf₂ : LowerSemicontinuous f₂
  cf₁ : ConvexOn ℝ Set.univ f₁
  cf₂ : ConvexOn ℝ Set.univ f₂
  nonempty :
    ∃ x₁ x₂, (A₁ x₁) + (A₂ x₂) - b = 0 ∧
      IsMinOn (fun (x : E₁ × E₂) => f₁ x.1 + f₂ x.2) Set.univ (x₁, x₂)
```

**读法**：Lean 的 `class` 就像论文开头 “Assumptions (A1)(A2)...” 的打包。  
后续 lemma 只要写 `[OptProblem ...]` 即自动获得这些假设。

---

### 2.2 ADMM：`ADMM`（迭代序列 + 更新规则）
对应论文里：`x₁(k), x₂(k), y(k), ρ_k` 以及三步更新（两次 argmin + 一次对偶更新）。

```plain
class ADMM (E₁ E₂ F : Type*) extends OptProblem E₁ E₂ F := where
  x₁ : ℕ → E₁
  x₂ : ℕ → E₂
  y  : ℕ → F
  ρₙ : ℕ → ℝ
  τ  : ℝ
  hρₙ_pos : ∀ k, ρₙ k > 0

  itex₁ : ∀ k, IsMinOn
    (fun x₁ => Augmented_Lagrangian_Function (toOptProblem) (ρₙ (k+1)) (x₁, x₂ k, y k))
    Set.univ (x₁ (k+1))

  itex₂ : ∀ k, IsMinOn
    (fun x₂ => Augmented_Lagrangian_Function (toOptProblem) (ρₙ (k+1)) (x₁ (k+1), x₂, y k))
    Set.univ (x₂ (k+1))

  itey : ∀ k,
    y (k+1) = y k + (τ * ρₙ (k+1)) • ((A₁ (x₁ (k+1))) + (A₂ (x₂ (k+1))) - b)
```

**关键点**：Lean 不要求显式写出 argmin 的解析解；你只需要用 `IsMinOn` 表达“它确实是子问题最小点”。  
这正是收敛分析所需的最小信息。

---

### 2.3 收敛目标：KKT 命题 `Convex_KKT`
对应论文：极限点满足最优性（次梯度/对偶）+ 原始可行。

```plain
class Convex_KKT (x₁ : E₁) (x₂ : E₂) (y : F) (opt : OptProblem E₁ E₂ F) : Prop where
  subgrad₁ : -(ContinuousLinearMap.adjoint opt.A₁) y ∈ SubderivAt opt.f₁ x₁
  subgrad₂ : -(ContinuousLinearMap.adjoint opt.A₂) y ∈ SubderivAt opt.f₂ x₂
  eq       : (opt.A₁ x₁) + (opt.A₂ x₂) = opt.b
```

---

## 3. 通用收敛层：势函数 + 递推 → 残差趋零、有界、极限点 KKT
### 3.1 选参考 KKT 点（比较点）
对应论文里：固定一个解 `(x', z', y')`，然后研究误差序列。

```plain
structure Existance_of_kkt (admm : ADMM E₁ E₂ F) where
  x₁ : E₁
  x₂ : E₂
  y  : F
  h  : Convex_KKT x₁ x₂ y admm.toOptProblem
```

---

### 3.2 定义误差序列与势函数（Lyapunov）
对应论文：定义 `e₁,e₂,e_y` 和一个能量函数 `g(k)`。

```plain
def e₁ (n : ℕ) : E₁ := admm.x₁ n - kkt.x₁
def e₂ (n : ℕ) : E₂ := admm.x₂ n - kkt.x₂
def ey (n : ℕ) : F  := admm.y  n - kkt.y

def g1 (n : ℕ) : ℝ :=
  ‖ey n‖^2
  + admm.τ * (admm.ρₙ n)^2 * ‖admm.A₂ (e₂ n)‖^2
  + admm.τ * (T_HWY - admm.τ) * (admm.ρₙ n)^2 *
      ‖admm.A₁ (admm.x₁ n) + admm.A₂ (admm.x₂ n) - admm.b‖^2
```

> 直觉：你把“收敛性”转换成“一个非负实数列满足递推并下降”。
>

---

## 4. 自适应条件：把“ρ 的变化可控”抽象成可复用接口（C1/C2）
### 4.1 以 C1 为例：增长可控的 `η_k`
```plain
def η_k (n : ℕ) : ℝ :=
  if n = 0 then 0
  else if admm.ρₙ (n+1) > admm.ρₙ n
    then Real.sqrt ((admm.ρₙ (n+1) / admm.ρₙ n)^2 - 1)
    else 0
```

### 4.2 C1 条件（核心字段：`∑ η^2`、`∏ (1+η^2)`）
```plain
class Condition_C1 ... (admm : outParam (ADMM E₁ E₂ F)) ... : Prop := where
  eta_square_summable' :
    Summable (fun n => (η_k (admm:=admm) n)^2)

  one_eta_square_multipliable :
    Multipliable (fun n => 1 + (η_k (admm:=admm) n)^2)
```

**读法**：这就是论文里“自适应罚参数变化足够温和”的条件化表达。  
有了它，就能把 C1 情况的收敛证明写成**通用定理**。

---

## 5. 通用收敛定理：满足 C1/C2 ⇒ ADMM 收敛（Lean 的最终定理形状）
Lean 用 `Tendsto` 表达收敛（`x_n → x*`）：

```plain
theorem adaptive_admm_convergence_c1 ... :
  ∃ (x₁* : E₁) (x₂* : E₂) (y* : F),
    Convex_KKT x₁* x₂* y* admm.toOptProblem ∧
      (Tendsto admm.x₁ atTop (𝓝 x₁*) ∧
       Tendsto admm.x₂ atTop (𝓝 x₂*) ∧
       Tendsto admm.y  atTop (𝓝 y*)) := by
  -- 这里内部是势函数递推 → 有界性/残差趋零 → 子列极限 → KKT → 整列收敛
  ...
```

> “存在一个 KKT 三元组，并且 (x₁,x₂,y) 三个序列都收敛到它。”
>

## 5.1 通用证明里“收敛的 KKT 点”是如何被构造出来的（不是算法计算，而是**从子列极限抽取**）
“通用证明过程中会不会具体找到那个收敛的 KKT 点？”——答案是：**会在逻辑上“构造出一个候选极限点”，并证明它是 KKT**。  
但这不是“按公式算出来”的，而是用**有限维有界序列 ⇒ 存在收敛子列**（Bolzano–Weierstrass/紧性）抽取出来的。

### 第一步：先证明迭代点整体有界（为抽子列做准备）
通用证明会先推出三元组序列 `(x₁ n, x₂ n, y n)` 有界，例如在 C1 情况下有：

```plain
lemma xy_isBounded_c1 ... : IsBounded (Set.range (fun n => (x₁ n, x₂ n, y n))) := ...
```

> 这里的有界性通常来自势函数递推（Lyapunov）+ C1/C2 的可和/可乘控制。
>

### 第二步：用“有界 ⇒ 存在收敛子列”抽取子列并**定义极限点**
你在 `AdaptiveTheorem_converge_c1.lean` 里把这一段包装得很清晰：先定义一个结构体把“子列 + 极限点”存起来：

```plain
structure Converge_Subseq_1 [Condition_C1 admm admm_kkt] where
  x₁'' : E₁
  x₂'' : E₂
  y''  : F
  φ    : ℕ → ℕ
  hphi : StrictMono φ
  hconverge :
    Tendsto (fun n => (x₁ (φ n), x₂ (φ n), y (φ n))) atTop (𝓝 (x₁'', x₂'', y''))
```

然后用 `tendsto_subseq_of_bounded` 从有界性中抽出这组数据（注意这里用到了 `choose`，本质是经典选择原理）：

```plain
def Subseq_c1 ... : Converge_Subseq_1 := by
  let x := tendsto_subseq_of_bounded (xy_isBounded_c1 fullrank₁ fullrank₂)
              (inSet (fun n => (x₁ n, x₂ n, y n)))
  choose x hx using x
  choose φ hphi1 using hx.2
  exact { x₁'' := x.1, x₂'' := x.2.1, y'' := x.2.2, φ := φ
        , hphi := hphi1.1, hconverge := hphi1.2 }
```

**读法**：这里的 `x₁'' x₂'' y''` 就是“通用证明里找到的候选收敛点”，它是某个收敛子列的极限。

### 第三步：证明这个子列极限点满足 KKT条件（次梯度闭性 + 可行性）
证明：

+ 次梯度条件：利用“次梯度图像闭性”（例如 `Image_subgradient_closed`）
+ 约束可行：利用残差趋零 + 连续性把极限带进去

最终组装成：

```plain
lemma Iskktpair_c1 ... : Convex_KKT x₁'' x₂'' y'' admm.toOptProblem :=
{ subgrad₁ := A₁'y_inthesubgradient_c1 fullrank₁ fullrank₂
, subgrad₂ := A₂'y_inthesubgradient_c1 fullrank₁ fullrank₂
, eq       := Satisfying_equational_constraint_c1 fullrank₁ fullrank₂ }
```

### 第四步：再证明“整列收敛”到这个极限点，并把它作为最终定理的见证
最后在总定理里直接把这个 `x₁'' x₂'' y''` 作为存在量返回：

```plain
theorem adaptive_admm_convergence_c1 ... :
  ∃ x₁* x₂* y*, Convex_KKT x₁* x₂* y* admm.toOptProblem ∧
    (Tendsto x₁ atTop (𝓝 x₁*) ∧ Tendsto x₂ atTop (𝓝 x₂*) ∧ Tendsto y atTop (𝓝 y*)) :=
⟨x₁'', x₂'', y'', Iskktpair_c1 fullrank₁ fullrank₂,
  x₁_converge_c1 fullrank₁ fullrank₂,
  x₂_converge_c1 fullrank₁ fullrank₂,
  y_converge_c1  fullrank₁ fullrank₂⟩
```

> 结论：**通用证明确实“找到/构造”了一个收敛的 KKT 点**，它来自“有界序列的收敛子列极限”。  
这在逻辑上是存在性构造（用经典选择），不是可计算构造（不会给出显式公式）。
>

---

### 6. Strategy3：如何“接入”到通用收敛定理（策略证明不是重做收敛分析）
### 6.1 Strategy3 只描述 ρ 的更新规则 + τₙ 可和
```plain
class Strategy3 (admm : ADMM E₁ E₂ F) : Prop where
  tau_seq : ℕ → ℝ
  h_tau_nonneg   : ∀ n, 0 ≤ tau_seq n
  h_tau_summable : Summable tau_seq
  h_rho_update : ∀ n,
    admm.ρₙ (n+1) = admm.ρₙ n * (1 + tau_seq n) ∨
    admm.ρₙ (n+1) = admm.ρₙ n / (1 + tau_seq n) ∨
    admm.ρₙ (n+1) = admm.ρₙ n
```

### 6.2 Strategy3 的“关键工作”：提供 `Condition_C1` 的实例
```plain
instance strategy3_satisfies_C1 (admm : ADMM E₁ E₂ F) [Strategy3 admm] ... :
  Condition_C1 ... (admm:=admm) ... := by
  -- 证明 eta^2 可和 + (1+eta^2) 可乘
  -- 然后组装成 Condition_C1 的字段
  ...
```

> 关键在于创建收敛条件的实例
>

### 6.3 Strategy3 收敛定理：套用通用收敛定理
```plain
theorem strategy3_converges (admm : ADMM E₁ E₂ F) [Strategy3 admm] ... :
  ∃ x₁* x₂* y*,
    Convex_KKT x₁* x₂* y* admm.toOptProblem ∧
      (Tendsto admm.x₁ atTop (𝓝 x₁*) ∧
       Tendsto admm.x₂ atTop (𝓝 x₂*) ∧
       Tendsto admm.y  atTop (𝓝 y*)) := by
  -- 关键：Strategy3 ⇒ Condition_C1 ⇒ 调用总定理
  apply adaptive_admm_convergence_c1
```

---

## 7. 如何复用这套框架：新增一个自适应策略要做什么
如果你要添加一个新策略 `StrategyX`，通常只做两步：

1. 写出策略 class（描述 `ρ_{k+1}` 如何由 `ρ_k` 更新 + 需要的可和/有界假设）  
2. 证明它能实例化 `Condition_C1` 或 `Condition_C2`（即给出字段：`Summable ...`、`Multipliable ...`）

完成后就可以：

```plain
theorem strategyX_converges ... := by
  apply adaptive_admm_convergence_c1   -- 或 c2
```

---

## 8. 文件对应关系（用于论文/README）
+ `AdaptiveScheme.lean`：`OptProblem`, `ADMM`, `Convex_KKT`（建模）
+ `AdaptiveLemmas.lean`：误差、势函数、通用引理（收敛骨架）
+ `AdaptiveCondition1.lean`：C1、`η_k`、与递推相关的关键估计
+ `AdaptiveCondition2.lean`：C2、`θ_k`、与递推相关的关键估计
+ `AdaptiveInv_bounded.lean`：由 `A x` 的有界/趋零反推 `x`（满秩/注入性相关）
+ `AdaptiveTheorem_converge_c1.lean`：总收敛定理（C1）
+ `AdaptiveTheorem_converge_c2.lean`：总收敛定理（C2）
+ `Strategy3_Convergence.lean`：Strategy3 ⇒ Condition_C1 ⇒ 收敛



## ![](fig/image.png)
