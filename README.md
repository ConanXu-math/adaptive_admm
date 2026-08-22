# Adaptive ADMM in Lean

这个仓库保存 Adaptive ADMM 收敛性分析的 Lean 4 形式化。当前主发布面是
`Optlib/Algorithm/AdaptiveADMM/`：证明核心、类型化策略接口和可复用的
$\tau$ 序列模板都由 Lean 检查。

历史 Python、LLM 和 OpenEvolve 生成器源码仍保留在 `lean_admm/`，用于追溯早期
实验；它们不是当前形式化的可信入口，也不自动保证任意候选策略能够通过证明。

## 当前状态

| 层次 | 状态 | 验收方式 |
| --- | --- | --- |
| C1 收敛定理 | Lean 已检查 | `adaptive_admm_convergence_c1` |
| C2 收敛定理 | Lean 已检查 | `adaptive_admm_convergence` |
| Strategy3 类型化桥接 | Lean 已检查 | `Strategy3.converges_from_policy` |
| $\tau$ 模板库 | Lean 已检查 | p-series、shifted p-series、geometric、有限和、smooth-as-sum、bounded modulation |
| 三个证书示例 | 分别由 Lean 编译 | `examples/*/certificate.lean` |
| 历史搜索/生成器 | legacy 源码 | 不属于 v2 证明门禁 |

## 形式化结论的范围

在相应的 C1 或 C2 条件、`Setting` 假设以及 $A_1$、$A_2$ 的单射假设下，核心定理
给出一个 KKT 点，并证明 ADMM 的 $x_1$、$x_2$、$y$ 迭代序列分别收敛到该点的
对应分量。

策略层把当前可复用的 Strategy3 条件封装为：

- `CertifiedTau`：包含非负序列 $\tau_n$ 及其可和性证明；
- `RhoAction`：每步只允许 increase、decrease 或 keep；
- `StrategyPolicy`：把 $\tau_n$ 与动作序列组合成类型化策略；
- `Strategy3.converges_from_policy`：在实际 $\rho_n$ 递推与该策略一致时复用 C1
  收敛证明。

这些结果不表示：任意 Python/LLM 策略会自动获得证明、生成器本身已被形式化验证、
或某个自适应规则在数值性能上优于其他规则。每个新策略仍需提供自己的 Lean 证书并
通过仓库门禁。

## 稳定入口

新证书只需导入：

```lean
import Optlib.Algorithm.AdaptiveADMM.Strategies
```

主要文件：

| 路径 | 职责 |
| --- | --- |
| `Optlib/Algorithm/AdaptiveADMM/AdaptiveScheme.lean` | Adaptive ADMM 的基本对象与迭代结构 |
| `Optlib/Algorithm/AdaptiveADMM/AdaptiveCondition1.lean` | C1 条件 |
| `Optlib/Algorithm/AdaptiveADMM/AdaptiveCondition2.lean` | C2 条件 |
| `Optlib/Algorithm/AdaptiveADMM/AdaptiveTheorem_converge_c1.lean` | C1 收敛定理 |
| `Optlib/Algorithm/AdaptiveADMM/AdaptiveTheorem_converge_c2.lean` | C2 收敛定理 |
| `Optlib/Algorithm/AdaptiveADMM/AdaptiveProductBounds.lean` | 实数乘积界的局部辅助引理 |
| `Optlib/Algorithm/AdaptiveADMM/Strategies/StrategyPolicy.lean` | 公开的类型化策略接口 |
| `Optlib/Algorithm/AdaptiveADMM/Strategies/TauTemplates.lean` | 可认证 $\tau$ 模板 |
| `Optlib/Algorithm/AdaptiveADMM/Strategies.lean` | 策略证书的稳定 facade |

策略子目录的设计与生成产物边界见
[`Optlib/Algorithm/AdaptiveADMM/Strategies/README.md`](Optlib/Algorithm/AdaptiveADMM/Strategies/README.md)，
完整发布边界见 [`doc/FORMALIZATION_SCOPE.md`](doc/FORMALIZATION_SCOPE.md)。

## 示例

`examples/` 包含三个已检查的策略证书：

1. 两项标准 p-series 之和；
2. shifted p-series 与 geometric 项的局部组合；
3. 两项 shifted p-series 的因式分解组合。

每个目录中的 `candidate.py` 和 `contract_result.json` 是生成输入/中间合约的溯源快照；
形式化结论由同目录的 `certificate.lean` 承担。详见
[`examples/README.md`](examples/README.md)。

## 本地验证

工具链固定在 `leanprover/lean4:v4.24.0-rc1`，依赖版本记录在
`lake-manifest.json`。首次运行需要网络下载依赖。

```bash
# 构建公开策略入口及其 C1 依赖
lake build Optlib.Algorithm.AdaptiveADMM.Strategies

# 构建 C2 收敛定理
lake build Optlib.Algorithm.AdaptiveADMM.AdaptiveTheorem_converge_c2

# 构建 Optlib 的默认目标
lake build

# 严格参数下复查公开入口
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false \
  Optlib/Algorithm/AdaptiveADMM/Strategies.lean

# 分别编译示例证书
find examples -name certificate.lean -print0 | \
  xargs -0 -n1 lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false
```

Adaptive ADMM 和仓库内较早的标准 ADMM 模块都使用顶层 `ADMM` 声明，不能在同一
Lean 环境中由一个聚合文件同时导入。因此 CI 分别构建默认目标、Adaptive ADMM
策略入口和 C2 定理；三个目标全部通过才算完成本仓库的构建门禁。

GitHub Actions 还会拒绝活跃形式化和示例中出现 `sorry`、`admit` 或新增的
`axiom` 声明。

## 仓库边界

- `Optlib/Algorithm/AdaptiveADMM/`：当前可信的形式化核心。
- `examples/`：具体候选到 Lean 证书的可读样例。
- `lean_admm/`：历史搜索和翻译源码，仅作 legacy 参考。
- 已提交的 checkpoints、日志、缓存、IDE 元数据和旧占位样例已从 v2 发布面移除；
  它们仍可从 Git 历史恢复。

## License

本仓库采用 [`LICENSE.txt`](LICENSE.txt) 中的 Apache License 2.0。
