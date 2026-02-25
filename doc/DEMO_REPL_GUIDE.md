# `demo_repl.py` 操作指南（环境配置到验证）

这份文档对应脚本：`demo_repl.py`  
目标：用本地 `lake env lean` 对 Lean 代码做编译验证，并拿到可读错误信息。

---

## 0. 从零初始化 Lean 项目（命令行）

如果你是新机器/新目录，可以直接按下面顺序执行：

```bash
# 0.1 安装 Lean 工具链（已安装可跳过）
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source "$HOME/.elan/env"

# 0.2 新建 Lean 项目
lake new optlib
cd optlib

# 0.3 添加 mathlib 依赖
lake add mathlib

# 0.4 拉取并编译依赖
lake update
lake build
```

最小验证：

```bash
cat > TempTest.lean <<'EOF'
import Mathlib
example : 1 + 1 = 2 := by decide
EOF

lake env lean TempTest.lean
```

---

## 1. 前置环境

### 1.1 Lean / Lake

先确认本机有 Lean4 工具链（`elan` + `lake`）：

```bash
lake --version
```

如果提示找不到命令，先安装 Lean4（elan）。

### 1.2 项目依赖（Mathlib 等）

在项目根目录（`optlib`）执行：

```bash
lake update
lake build
```

说明：
- `lake env lean` 会使用当前项目的依赖环境；
- 没有先 `update/build`，常见报错是 import 找不到。

### 1.3 Python 环境

`demo_repl.py` 只用标准库（`subprocess`、`os`），Python 3 即可：

```bash
python --version
```

---

## 2. 脚本做了什么（对应 `demo_repl.py`）

`run_lean_locally(lean_code, file_name="TempTest.lean")` 的流程：

1. 把 `lean_code` 写到 `TempTest.lean`
2. 执行：
   ```bash
   lake env lean TempTest.lean
   ```
3. 根据返回码给出结构化结果：
   - `returncode == 0`：编译通过
   - 否则：收集 `stderr/stdout` 作为错误详情返回

---

## 3. 如何运行

在项目根目录执行：

```bash
python demo_repl.py
```

你会看到两类输出之一：

- 成功：
  - `✅ 编译通过！完美！`
- 失败：
  - `❌ 编译失败 (exit=...)`
  - 后面跟 `----------- 报错详情 -----------`

---

## 4. 换成你自己的 Lean 代码

有两种方式：

### 方式 A：直接改脚本里的 `agent_code`

编辑 `demo_repl.py` 中的 `agent_code = """..."""`，再运行脚本。

### 方式 B：在其他 Python 代码里复用

```python
from demo_repl import run_lean_locally

code = """
import Mathlib
example : 1 + 1 = 2 := by decide
"""

feedback = run_lean_locally(code, "TempTest.lean")
print(feedback)
```

---

## 5. 常见报错与处理

### 报错：`找不到 'lake' 命令`

原因：Lean4 工具链未安装或 PATH 未生效。  
处理：安装/修复 elan，并重开终端后再试。

### 报错：`Unknown identifier ...`

原因：Lean 代码缺少 import，或符号名拼错。  
处理：补全对应 `import`，例如凸函数相关常用：

```lean
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Function
```

### 报错详情为空（以前可能出现）

当前脚本已处理：若 `stderr/stdout` 都为空，会返回 `<no stderr/stdout output>`，避免“失败但看不到原因”。

---

## 6. 建议的日常工作流

1. 在 Python 侧生成/修改 Lean 代码
2. 调 `run_lean_locally(...)` 获取编译反馈
3. 按报错修正 Lean 代码
4. 循环直到 `success=True`

这个流程不依赖 LeanDojo，适合本地快速迭代验证。

---

## 7. 针对你当前仓库（`optlib`）的最短命令

如果你已经在当前项目里，直接在项目根目录执行：

```bash
lake update
lake build
python demo_repl.py
```

这样就会走本文档同一套“写入 `TempTest.lean` + `lake env lean` 验证”的流程。

