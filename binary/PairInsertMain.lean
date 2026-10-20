import SourceAdapter
import PairInsert
open Lean Leanux Leanux.WG Binary.Pair

def runCase (input : ProbeInput) (label : String) (w : World)
    (calls : List (IndexOwner × List HiddenRecord)) (preempt : Nat := 0) : Except String Json := do
  let mut runs := #[]
  for seed in [(0 : UInt64),0xffffffffffffffff] do
    let mut s ← Replace.fixture input w
    s := {s with binary := {s.binary with state := {s.binary.state with data := {
      s.binary.state.data with dmem := put s.binary.state.data.dmem input.preempt 4 preempt}}}}
    let mut reports := #[]
    for (owner,records) in calls do
      s := {s with world := {s.world with ambient := {s.world.ambient with hidden := some records}}}
      let (next,report) ← (Insert.invoke input seed s owner).mapError (fun e => s!"{label}: {e}")
      unless next.world.hidden==some [] do throw s!"{label}: unconsumed input"
      s := next
      reports := reports.push report
    runs := runs.push (Json.mkObj [("seed",toJson seed.toNat),("calls",toJson reports)])
  return Json.mkObj [("case",toJson label),("runs",toJson runs)]

def suite (input : ProbeInput) : Except String Json := do
  let w ← replayRecordedPrefix input.trace input.operation
  let some d := w.wg.dev | throw "insert prefix: no device"
  let [first,second] := d.peerList | throw "insert pilot requires two recorded peers"
  unless d.indexTable.isEmpty do throw "insert pilot requires no already linked entries"
  let t ← Runner.parseTrace input.trace
  let some hidden := t.hidden | throw "insert pilot requires recorded inputs"
  let draws := hidden.toList.flatten.filter (·.site==HiddenSite.indexDraw.info.id)
  let [a,b,c] := draws | throw "insert pilot requires exactly three recorded draws"
  let (av,_) ← Insert.draw [a]
  let (bv,_) ← Insert.draw [b]
  let (cv,_) ← Insert.draw [c]
  unless av==bv && av != cv do throw "insert pilot collision records differ"
  let firstOwner := IndexOwner.handshake first
  let secondOwner := IndexOwner.handshake second
  let mut cases := #[← runCase input "recorded-prefix/selected-insertions" w
    [(firstOwner,[a]),(secondOwner,[b,c])]]
  let inputRecord (v : Nat) := Insert.record (.ofNat v)
  for collisions in [0,1,8,32] do
    cases := cases.push (← runCase input s!"synthetic/retries-{collisions}-and-reinsertion" w
      [(firstOwner,[inputRecord 7]),(secondOwner,List.replicate collisions (inputRecord 7)++[inputRecord 8199]),
       (firstOwner,[inputRecord 8199,inputRecord 16391]),(secondOwner,[inputRecord 0])])
  cases := cases.push (← runCase input "synthetic/wrapped-preempt-nested-pending-read" w
    [(firstOwner,[inputRecord 7]),(secondOwner,[inputRecord 7,inputRecord 8199])] 0xfffffe00)
  let s ← Replace.fixture input w
  let badCases := [("missing",[]),("wrong-site",[{a with site := 0}]),
    ("short",[{a with bytes := a.bytes.take 4}]),
    ("padding",[{a with bytes := a.bytes.take 4++[1,0,0,0]}])]
  let mut controls := #[]
  for (name,records) in badCases do
    let bad := {s with world := {s.world with ambient := {s.world.ambient with hidden := some records}}}
    match Insert.invoke input 0 bad firstOwner with
    | .ok _ => throw s!"insert input control unexpectedly passed: {name}"
    | .error e =>
      unless e.startsWith "insert.input." do throw s!"insert input control failed elsewhere: {name}: {e}"
      controls := controls.push (Json.mkObj [("case",toJson name),("rejected",toJson e)])
  let badMemory := put (put s.binary.state.data.dmem input.preempt 4 0xfffffe00)
    Binary.TrustBase.softirqPendingAddress.toNat 2 1
  let bad := {s with
    world := {s.world with ambient := {s.world.ambient with hidden := some [inputRecord 7]}}
    binary := {s.binary with state := {s.binary.state with data := {s.binary.state.data with dmem := badMemory}}}}
  let pendingControl ← match Insert.invoke input 0 bad firstOwner with
    | .ok _ => throw "nested pending-softirq control unexpectedly passed"
    | .error e => do
      unless e=="insert.call.nested-pending-softirq" do throw s!"nested pending control failed elsewhere: {e}"
      pure (Json.mkObj [("case",toJson "wrapped-count/nonzero-pending"),("rejected",toJson e)])
  return Json.mkObj [("status",toJson "pass"),
    ("entry_origin",toJson "recorded-prefix and labelled generated heaps; not captured snapshots"),
    ("execution_scope",toJson "actual anchor, KCOV and BH instructions; supplied random-service returns"),
    ("cases",toJson cases),("input_controls",toJson controls),
    ("readiness_controls",toJson #[pendingControl])]

def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "usage: binary-pair-insert INPUT.json"; return 1
  let .ok input := Json.parse (← IO.FS.readFile path) >>= fromJson? (α := ProbeInput)
    | IO.eprintln "FAIL: invalid insertion input"; return 1
  match suite input with
  | .ok report => IO.println report.compress; return 0
  | .error e => IO.eprintln s!"FAIL: {e}"; return 1
