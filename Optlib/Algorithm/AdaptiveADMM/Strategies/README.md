# Adaptive ADMM 策略形式化

本目录只保存当前认证链复用的、人工维护的 Lean 源码。数值搜索候选、LLM
草稿和单次编译证书都属于运行产物，不应进入 `Optlib` 源码树。

## 保留模块

| 文件 | 职责 |
| --- | --- |
| `StrategyPolicy.lean` | 定义公开的 `RhoAction`、`CertifiedTau` 和 `StrategyPolicy` 类型化接口 |
| `Adaptive_Strategy_Convergence.lean` | 定义内部 `Strategy3` 证明合约、类型化桥接，以及历史证书兼容层 |
| `VerificationLib.lean` | 提供可和性等通用验证引理 |
| `AdaptiveStrategyBase.lean` | 提供标准残差动作、残差比例函数及历史整数方向兼容接口 |
| `TauTemplates.lean` | 登记可认证的 $\tau$ 模板及其可和性证明 |

`residualBalanceAction` 只用于精确采用标准残差阈值的策略。通用生成证书应向
`StrategyPolicy` 传入任意 `action : ℕ → RhoAction`，从而保留候选自己的确定性
分支选择；Python contract 另行检查每个 rho 写入是否仍属于三态更新。

目录上一级的 `Strategies.lean` 是生成证书的唯一公开入口。新证书应只导入：

```lean
import Optlib.Algorithm.AdaptiveADMM.Strategies
```

依赖方向为：

```text
AdaptiveTheorem_converge_c1 ─┐
StrategyPolicy ──────────────┴─> Adaptive_Strategy_Convergence
Adaptive_Strategy_Convergence + VerificationLib ─> AdaptiveStrategyBase
VerificationLib ──────────────────────────────────> TauTemplates
AdaptiveStrategyBase + TauTemplates ──────────────> Strategies facade
```

## 生成产物边界

- Harness 生成的候选证书写入该候选的 `experiments/` 证据目录。
- 旧 evaluator 的临时证书写入 `experiments/legacy_evaluator/formal_candidates/`。
- 旧 LLM 翻译链的结果写入 `experiments/legacy_translate/formal_candidates/`。
- 不在本目录保存 `generated_prove_*.lean`、`auto_update_rho_llm_*.lean` 或带
  `sorry`、`admit` 的草稿。

## 验证

从 `lean_workspace/` 执行：

```bash
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false \
  Optlib/Algorithm/AdaptiveADMM/Strategies.lean
lake build
```
