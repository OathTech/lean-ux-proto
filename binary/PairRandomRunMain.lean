import PairRandomRun
open Lean

def main : IO UInt32 := do
  match Binary.Pair.RandomRun.suite with
  | .ok result => IO.println result.compress; return 0
  | .error error => IO.eprintln s!"FAIL: {error}"; return 1
