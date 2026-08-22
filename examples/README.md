# Checked Strategy Certificates

本目录给出三个具体策略如何通过公开入口接入 Strategy3 收敛定理。每个示例包含：

| 文件 | 作用 | v2 门禁 |
| --- | --- | --- |
| `candidate.py` | 数值策略输入的只读快照 | 不执行 |
| `contract_result.json` | 确定性合约抽取结果的只读快照 | 不作为证明 |
| `certificate.lean` | 将策略包装为 `CertifiedTau` 与 `StrategyPolicy`，调用收敛定理 | Lean 编译 |
| `notes.md` | 解释对应的证明模式 | 文档审查 |

三个模式分别是：

1. `01_standard_pseries_sum2`：两项标准 p-series 之和；
2. `02_local_atom_sum`：shifted p-series 与 geometric 项之和；
3. `03_factored_atom_sum`：两项 shifted p-series 的组合。

单独验证全部证书：

```bash
lake build Optlib.Algorithm.AdaptiveADMM.Strategies
find examples -name certificate.lean -print0 | \
  xargs -0 -n1 lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false
```

这些示例只证明各自证书在所列假设下成立，不证明任意 Python 策略都能自动转译或
自动获得收敛性证明。
