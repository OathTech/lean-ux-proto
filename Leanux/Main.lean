import Leanux.Runner

/-- A fresh Files state is created for each JSONL trace. Invalid input stops
    with an error on stderr and a nonzero exit, never a success observation. -/
def main : IO UInt32 := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  let errors ← IO.getStderr
  repeat
    let line ← input.getLine
    if line.isEmpty then return 0
    if line.utf8ByteSize > 65536 then
      errors.putStrLn "invalid input: trace line exceeds 65536 bytes"
      return 2
    match Lean.Json.parse line >>= Leanux.Runner.parseTrace with
    | .error message =>
      errors.putStrLn s!"invalid input: {message}"
      return 2
    | .ok trace =>
      output.putStrLn (Leanux.Runner.executeTrace trace).compress
      output.flush
  return 0
