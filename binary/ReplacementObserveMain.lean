import ReplacementObserve

open Lean Binary.ReplacementObserve

def main (args : List String) : IO UInt32 := do
  let [inputPath, operationText, ordinalText] := args
    | IO.eprintln "usage: binary-replacement-observe INPUT.json OPERATION ORDINAL"; return 1
  let some operation := operationText.toNat? | IO.eprintln "invalid operation"; return 1
  let some ordinal := ordinalText.toNat? | IO.eprintln "invalid ordinal"; return 1
  let parsed := Json.parse (← IO.FS.readFile inputPath) >>= fromJson? (α := ProbeInput)
  match parsed >>= fun input => select input operation ordinal with
  | .ok selection => IO.println (report selection operation ordinal).compress; return 0
  | .error error => IO.eprintln s!"FAIL: {error}"; return 1
