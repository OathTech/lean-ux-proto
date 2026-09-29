import Leanux.Runner

/-- Reads JSONL traces on stdin and writes one observation per trace. A fresh
    kernel state is created for each trace. Invalid input (exit 2), a path the
    mirror does not model (exit 3), or a mirror invariant failure (exit 4)
    stops with a message on stderr, never a success observation. `--decisions` prints the
    decision table instead. -/
def main (args : List String) : IO UInt32 := do
  let output ← IO.getStdout
  let errors ← IO.getStderr
  if args == ["--decisions"] then
    output.putStrLn Leanux.Runner.decisionsJson.compress
    return 0
  if !args.isEmpty then
    errors.putStrLn "usage: leanux-model [--decisions] < traces.jsonl"
    return 2
  let input ← IO.getStdin
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
      match Leanux.Runner.executeTrace trace with
      | .error (index, stop) =>
        errors.putStrLn s!"trace {trace.id} operation {index}: {stop.message}"
        -- 3: the C leaves the modeled domain; 4: a mirror defect
        return match stop with | .outsideDomain .. => 3 | .invariant _ => 4
      | .ok json =>
        output.putStrLn json.compress
        output.flush
  return 0
