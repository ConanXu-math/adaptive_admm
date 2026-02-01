import subprocess
import os

def run_lean_locally(lean_code, file_name="TempTest.lean"):
    """
    在本地运行 Lean 代码，无需 Git，无需 LeanDojo。
    """
    
    # 1. 把 Agent 生成的代码写入文件
    # 注意：必须把依赖的 import 写全，否则编译不过
    full_content = lean_code
    
    with open(file_name, "w", encoding="utf-8") as f:
        f.write(full_content)
        
    print(f"📝 代码已写入 {file_name}，准备编译...")

    try:
        # 2. 调用本地的 Lean 编译器
        # 使用 'lake env lean' 是为了确保能找到 mathlib 等库
        # capture_output=True 会把屏幕上的字抓下来给 Python
        result = subprocess.run(
            ["lake", "env", "lean", file_name],
            capture_output=True,
            text=True,
            check=False # 即使报错也不要抛出异常，我们要捕获报错信息
        )
        
        # 3. 分析结果 (这是 Agent 的反馈来源)
        if result.returncode == 0:
            return {
                "success": True,
                "message": "✅ 编译通过！完美！",
                "output": result.stdout
            }
        else:
            stderr_text = (result.stderr or "").strip()
            stdout_text = (result.stdout or "").strip()
            combined = "\n".join([t for t in [stderr_text, stdout_text] if t])
            if not combined:
                combined = "<no stderr/stdout output>"
            return {
                "success": False,
                "message": f"❌ 编译失败 (exit={result.returncode})",
                "error": combined
            }
            
    except FileNotFoundError:
        return {"success": False, "message": "❌ 找不到 'lake' 命令，请检查 Lean 4 是否安装正确。"}

# --- 测试案例 (模拟 Agent) ---

# 假设这是 Agent 写的代码（故意写错一点来看看报错）
agent_code = """import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Basic

open Real

-- Agent 尝试定义一个凸函数
def MySquare (x : ℝ) : ℝ := x ^ 2

-- 故意写错：把凸性 convex_on 写成了 convex_off (不存在的词)
lemma is_convex : ConvexOn ℝ Set.univ MySquare := by

"""

# 跑一下
feedback = run_lean_locally(agent_code)

if feedback["success"]:
    print(feedback["message"])
else:
    print(feedback["message"])
    print("----------- 报错详情 -----------")
    print(feedback["error"])
