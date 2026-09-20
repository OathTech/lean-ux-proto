#!/usr/bin/env python3
"""Run with the staged helper Python inside scripts/in-bundle."""
import asyncio
import json
import os
from pathlib import Path
import tempfile
from mcp import ClientSession, StdioServerParameters
from mcp.client.stdio import stdio_client

ROOT = Path(__file__).resolve().parents[1]
ARTIFACTS = Path(os.environ.get('LEANUX_ARTIFACTS', ROOT / '.artifacts'))
PROBES = ARTIFACTS / 'probes'
PROBES.mkdir(parents=True, exist_ok=True)
PROJECT = Path(tempfile.mkdtemp(prefix="lsp-", dir=PROBES))
(PROJECT / "lean-toolchain").write_text("leanprover/lean4:v4.33.1\n")
(PROJECT / "lakefile.toml").write_text('name = "lsp_probe"\n')
(PROJECT / "Main.lean").write_text("import Std\nexample (n : Nat) : n + 0 = n := by simp\n")
(PROJECT / "Broken.lean").write_text('import Std\ndef bad : Nat := "deliberate type error"\n')


async def check():
    env = os.environ.copy()
    env["LEAN_PROJECT_PATH"] = str(PROJECT)
    env["LEAN_MCP_DISABLED_TOOLS"] = (
        "lean_leansearch,lean_loogle,lean_leanfinder,lean_state_search,lean_hammer_premise"
    )
    args = StdioServerParameters(
        command=str(ROOT / "scripts/lean-lsp-python"),
        args=["-c", "from lean_lsp_mcp import main; main()"], env=env,
    )
    records = []
    async with stdio_client(args) as (reader, writer):
        async with ClientSession(reader, writer) as session:
            await session.initialize()
            for name in ("Main.lean", "Broken.lean"):
                response = await session.call_tool(
                    "lean_diagnostic_messages", {"file_path": str(PROJECT / name)})
                if response.isError or not response.structuredContent:
                    raise RuntimeError(f"Lean diagnostic request failed: {response}")
                result = response.structuredContent["result"]
                assert not result["timed_out"] and not result["partial"], result
                errors = [d for d in result["items"] if d["severity"] == "error"]
                if name == "Main.lean":
                    assert result["success"] and not errors, result
                else:
                    assert not result["success"] and any("Type mismatch" in d["message"] for d in errors), result
                records.append({"file": name, "result": result})
    (ARTIFACTS / 'provisioning').mkdir(parents=True, exist_ok=True)
    (ARTIFACTS / 'provisioning/lean-lsp-check.json').write_text(
        json.dumps(records, indent=2) + "\n")
    print("PASS: offline Lean MCP diagnostics accept valid code and detect a type error.")


asyncio.run(asyncio.wait_for(check(), 45))
