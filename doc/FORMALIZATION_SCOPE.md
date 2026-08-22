# Adaptive ADMM Formalization v2 发布边界

## 核心目标

把仓库的默认入口更新为当前可构建、无占位证明的 Adaptive ADMM Lean 形式化，同时让读者能区分“已由 Lean 检查的结论”和“历史实验流水线”。

## Keep

- `Optlib/` 及其当前证明依赖：它们共同构成可由 `lake build` 检查的 Lean 工程。
- `Optlib/Algorithm/AdaptiveADMM/` 的新版核心、策略接口与模板定理。
- 三个可独立编译的证书示例，覆盖标准 p-series、局部原子求和与因式分解原子求和。
- 历史 Python/LLM/OpenEvolve 源码，放在 `lean_admm/` 并明确标记为 legacy，供追溯旧实验使用。
- 本地构建、严格入口检查、示例编译与占位证明扫描。

## Defer

- 把新版确定性合约生成器整体迁入本仓库：只有当该仓库需要同时发布搜索/生成产品时再做。
- 自动从任意 Python 策略生成 Lean 证明：当前发布只承诺已纳入仓库的证明与证书。
- 扩展更多策略族或性能实验：应由新的数学声明、证明或可复现实验单独驱动。
- GitHub Release、远端 tag 与 `main` 合并：等本地分支审查通过后再执行。

## Delete

- 已提交的 OpenEvolve checkpoints、日志、压缩包和重复运行结果。
- 已提交的 `__pycache__`、`.pyc` 与 IDE 元数据。
- 旧 `sample1/`、`sample2/`、`sample3/`，其中包含与当前公开证明口径冲突的生成稿或占位证明。
- `AdaptiveADMM/Strategies/` 中已被新版策略层取代的 LLM 生成稿和旧兼容草稿。

以上删除仅发生在新分支；文件仍可从 Git 历史中的 `12c0e5481aa77fbb548f567bb55e563a6e11e823` 恢复。

## Do not cut

- 不删除 `Optlib/` 中新版证明所依赖的其他算法与分析模块。
- 不把 `sorry`、`admit` 或新增公理包装成“已形式化”。
- 不把本地构建成功表述为论文结论更强、算法性能更好或任意策略均可自动证明。
- 不推送远端，不改动用户原来的脏工作区。
- 保留完整构建和干净检出的可重复检查。

## 责任边界

| 组件 | 拥有 | 不拥有 | 原因 |
| --- | --- | --- | --- |
| `Optlib/Algorithm/AdaptiveADMM/` | Adaptive ADMM 定义、条件、收敛定理、策略证书 | Python 搜索、LLM 输出、实验日志 | Lean 核心应只依赖可检查的数学接口 |
| `Optlib/Algorithm/AdaptiveADMM/Strategies.lean` | 稳定公开导入入口 | 策略搜索或文件生成 | 下游只需依赖一个受控 facade |
| `examples/` | 已知可编译的策略证书 | 声称覆盖任意策略 | 示例只证明各自实例 |
| `lean_admm/` | 历史生成/搜索源码 | 当前证明验收标准 | 保留溯源，但不进入 v2 可信核心 |
| `.github/workflows/lean.yml` | 构建、严格入口、示例和占位证明门禁 | 数学结论设计 | CI 只验证仓库声明的机械检查 |

## 接口边界

| 调用方 | 被调用方 | 稳定接口 | 数据约束 | 失败行为 |
| --- | --- | --- | --- | --- |
| 下游 Lean 文件 | `Strategies.lean` | `StrategyPolicy`、`CertifiedTau`、策略模板与收敛定理 | 类型检查通过且无占位证明 | Lean 编译失败 |
| 示例证书 | 策略 facade | 每个示例的 `certificate.lean` | 独立执行 `lake env lean` | 非零退出 |
| GitHub Actions | Lake 工程 | `lake build` | 锁定的 `lean-toolchain` 与 `lake-manifest.json` | 工作流失败 |
| GitHub Actions | 活跃证明路径 | 占位证明扫描 | `Optlib/Algorithm/AdaptiveADMM` 和 `examples` 内不得出现 `sorry`、`admit`、`axiom` | 工作流失败 |

## 依赖方向

1. `Optlib` 基础数学模块 → Adaptive ADMM 核心模块。
2. Adaptive ADMM 核心模块 → `Strategies/` 的证书与模板。
3. `Strategies.lean` → 对外聚合稳定接口。
4. `examples/` → 只依赖稳定接口。
5. CI → 构建并检查以上路径；历史 `lean_admm/` 不反向进入可信核心。

## 已发现的边界违规

- 旧 README 把提案、生成流程和带 `sorry` 的兜底写成统一的“验证”流水线。
- checkpoints、日志、缓存和 IDE 文件被提交为产品源码，模糊了发布面。
- 旧样例与活跃形式化并列，其中存在实际占位证明。
- 多个生成的 `.lean` 文件直接放在策略核心目录，绕过稳定接口。

## 最小边界保持改动

1. 原样同步已经在源工程通过构建的 Adaptive ADMM 子树。
2. 从新分支删除生成产物、缓存和含占位证明的旧样例。
3. 只加入三个已通过 Lean 的代表性证书示例。
4. 重写 README，明确可信核心、结论范围、复现命令与 legacy 边界。
5. 增加同口径 CI，不迁移新的搜索平台或增加策略抽象。

## 验证

- `lake build` 必须成功。
- 严格参数下单独编译 `Optlib/Algorithm/AdaptiveADMM/Strategies.lean`。
- 分别编译三个 `examples/*/certificate.lean`。
- 活跃证明路径的占位证明扫描必须为空。
- `git diff --check` 必须成功，且已跟踪文件中不得残留 outputs、cache、IDE 元数据。
