#!/usr/bin/env python
"""
Entry point script for OpenEvolve
"""
import sys
from pathlib import Path

# 在导入 openevolve 前加载 .env，保证主进程和 worker 都能拿到 DEEPSEEK_API_KEY
try:
    from dotenv import load_dotenv
    load_dotenv()
    load_dotenv(Path(__file__).resolve().parent.parent / ".env")
    load_dotenv(Path(__file__).resolve().parent / "alpha_evolve" / ".env")
except ImportError:
    pass

from openevolve.cli import main

if __name__ == "__main__":
    sys.exit(main())
