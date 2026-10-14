import Leanux.Runner

/-- Reads JSONL traces on stdin and writes one observation per trace. A fresh
    kernel state is created for each trace. Invalid input (exit 2), a path the
    mirror does not model (exit 3), or a mirror invariant failure (exit 4)
    stops with a message on stderr, never a success observation; records that
    disagree with the mirror's hidden-input reads exit 5. `--decisions` prints
    the decision table and `--hidden-sites` the hidden-input sites instead. -/
def main (args : List String) : IO UInt32 := do
  let output ← IO.getStdout
  let errors ← IO.getStderr
  if args == ["--decisions"] then
    output.putStrLn Leanux.Runner.decisionsJson.compress
    return 0
  if args == ["--hidden-sites"] then
    output.putStrLn Leanux.Runner.hiddenSitesJson.compress
    return 0
  let domainOnly := args == ["--domain"]
  -- the flood summary's check mode (docs/2026-10-05-e-dos.md, the pre-release
  -- review's section 8): the invalid tail unsummarised
  let floodExact := (← IO.getEnv "LEANUX_FLOOD_EXACT") == some "1"
  if !args.isEmpty && !domainOnly then
    errors.putStrLn "usage: leanux-model [--decisions | --hidden-sites | --domain] < traces.jsonl"
    return 2
  let input ← IO.getStdin
  repeat
    let line ← input.getLine
    if line.isEmpty then return 0
    -- a bound on one trace's line: 1 MiB holds a trace with the longest programs
    -- the harness carries (three 768-instruction seccomp installs with their
    -- kind-309 records are about 80 KB; the old 64 KB refused them, X 2026-10-13)
    if line.utf8ByteSize > 1048576 then
      errors.putStrLn "invalid input: trace line exceeds 1048576 bytes"
      return 2
    match Lean.Json.parse line >>= Leanux.Runner.parseTrace with
    | .error message =>
      errors.putStrLn s!"invalid input: {message}"
      return 2
    | .ok trace =>
      -- `--domain` runs before Linux, without hidden-input records: their
      -- reads return placeholders, and the check's run is authoritative
      match Leanux.Runner.executeTrace trace (placeholders := domainOnly) (floodExact := floodExact) with
      | .error (index, .outsideDomain site what) =>
        if domainOnly then
          -- `--domain`: report whether each trace stays inside the modeled domain
          output.putStrLn (Lean.Json.mkObj [("id", Lean.toJson trace.id), ("in_domain", Lean.toJson false),
            ("index", Lean.toJson index), ("site", Lean.toJson site), ("what", Lean.toJson what)]).compress
        else
          errors.putStrLn s!"trace {trace.id} operation {index}: {(Leanux.Stop.outsideDomain site what).message}"
          return 3
      | .ok json =>
        if domainOnly then
          -- W2 (docs/2026-10-06-w1-w2-netlink.md 4.7): the trace's label count,
          -- measured offline by the generators against the check's cap
          let branches := match json.getObjVal? "branches" with
            | .ok (Lean.Json.arr labels) => labels.size
            | _ => 0
          output.putStrLn (Lean.Json.mkObj [("id", Lean.toJson trace.id), ("in_domain", Lean.toJson true),
            ("branches", Lean.toJson branches)]).compress
        else
          output.putStrLn json.compress
        output.flush
      | .error (index, stop) =>
        errors.putStrLn s!"trace {trace.id} operation {index}: {stop.message}"
        -- 4: a mirror defect, 5: hidden-input records that disagree with the
        -- mirror (3, outside the domain, is handled above)
        return match stop with | .outsideDomain .. => 3 | .invariant _ => 4 | .hidden _ => 5
  return 0
