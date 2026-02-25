# Lean ADMM 进化搜索运行说明

本文档说明如何运行 `lean_admm` 下的自适应 ADMM 策略进化搜索（OpenEvolve 入口）。

---

## 1. 命令格式

入口脚本：`lean_admm/search_admm.py`。**必须在项目根目录**（即 `adaptive admm` 仓库根）下执行，以便 evaluator 能正确找到 `Optlib` 与 Lean 环境。

### 1.1 基本用法（必填参数）

```bash
python lean_admm/search_admm.py \
  lean_admm/alpha_evolve/initial_program.py \
  lean_admm/alpha_evolve/evaluator.py
```

- **第一个参数 `initial_program`**：初始程序路径，内含被进化的 `update_rho` 等逻辑（`alpha_evolve/initial_program.py`）。
- **第二个参数 `evaluation_file`**：评估脚本路径，该模块需提供 `evaluate(program_path)` 函数（`alpha_evolve/evaluator.py`）。

### 1.2 带配置的完整示例

```bash
python lean_admm/search_admm.py \
  -c lean_admm/alpha_evolve/config.yaml \
  -o lean_admm/alpha_evolve/openevolve_output \
  -i 15 \
  lean_admm/alpha_evolve/initial_program.py \
  lean_admm/alpha_evolve/evaluator.py
```

---

## 2. 命令行参数说明

| 选项 | 说明 |
|------|------|
| `-c` / `--config` | 配置文件路径（YAML），如 `config.yaml`，用于 LLM、种群、评估等配置。 |
| `-o` / `--output` | 结果输出目录（checkpoint、best 程序等）。 |
| `-i` / `--iterations` | 最大迭代轮数。 |
| `-t` / `--target-score` | 达到该分数后提前停止。 |
| `--checkpoint` | 从指定 checkpoint 恢复，例如：`openevolve_output/checkpoints/checkpoint_50`。 |
| `--log-level` | 日志级别：`DEBUG` / `INFO` / `WARNING` / `ERROR` / `CRITICAL`。 |
| `--api-base` | LLM API 的 base URL。 |
| `--primary-model` | 主模型名称。 |
| `--secondary-model` | 副模型名称。 |

查看完整帮助：

```bash
python lean_admm/search_admm.py -h
```

---

## 3. 运行前准备

### 3.1 环境变量（API Key）

脚本会从以下位置加载 `.env`（按优先级）：

- 当前工作目录
- 项目根目录下的 `.env`
- `lean_admm/alpha_evolve/.env`

在配置中使用的 LLM 为 DeepSeek，需在 `.env` 中设置：

```bash
DEEPSEEK_API_KEY=your_api_key_here
```

未设置时，进化过程中的 LLM 调用会失败。

### 3.2 工作目录

- **必须**在仓库根目录（即包含 `lean_admm` 与 `Optlib` 的目录）下执行上述命令。
- evaluator 会基于 `evaluator.py` 所在位置计算 `Optlib` 与 `LEAN_PROJECT_ROOT`，并在此根目录下执行 `lake env lean` 做 Lean4 验证。

### 3.3 Lean 环境（可选，用于形式化验证）

若 evaluator 会跑 Lean4 验证（即对生成的策略做形式化检查），需保证：

1. 已安装 Lean4 工具链（`elan` + `lake`）。
2. 在项目根目录执行：

   ```bash
   lake update
   lake build
   ```

详见 `doc/DEMO_REPL_GUIDE.md` 中的 Lean 环境配置。

---

## 4. 输出与恢复

- 默认或通过 `-o` 指定的输出目录下会有：
  - `openevolve_output/checkpoints/checkpoint_*`：各轮 checkpoint。
  - `openevolve_output/best/`：当前最优程序及相关信息（如 `best_program.py`、`best_program_info.json` 等）。
- 从某轮恢复继续跑：

  ```bash
  python lean_admm/search_admm.py \
    --checkpoint lean_admm/alpha_evolve/openevolve_output/checkpoints/checkpoint_50 \
    -c lean_admm/alpha_evolve/config.yaml \
    lean_admm/alpha_evolve/initial_program.py \
    lean_admm/alpha_evolve/evaluator.py
  ```

---

## 5. 相关文件结构（简要）

| 路径 | 说明 |
|------|------|
| `lean_admm/search_admm.py` | OpenEvolve 入口，加载 `.env` 后调用 `openevolve.cli.main()`。 |
| `lean_admm/alpha_evolve/config.yaml` | 进化与 LLM 配置（迭代数、模型、种群、evaluator 超参等）。 |
| `lean_admm/alpha_evolve/initial_program.py` | 初始 `update_rho` 等实现，作为进化起点。 |
| `lean_admm/alpha_evolve/evaluator.py` | 实现 `evaluate(program_path)`，对候选程序做数值评估与可选的 Lean4 验证。 |
| `Optlib/` | Lean4 形式化库，evaluator 生成的证明会写至 `Optlib/Algorithm/AdaptiveADMM/Strategies/` 并在此工程下用 `lake env lean` 检查。 |

更多关于自适应 ADMM 与 Lean 证明流程的说明，见项目根目录的 `readme.md` 与 `readme-.md`。
