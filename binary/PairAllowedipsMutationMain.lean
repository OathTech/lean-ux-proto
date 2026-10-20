import PairAllowedipsMutation

open Lean Leanux Leanux.WG Binary.Pair.Allowedips

def initialWorld : World := {
  ambient := {env := Runner.harnessEnv,timing := Env.timing},
  tasks := Runner.initialTasks 1024 false false false,fs := {},
  wg := {dev := some {ifindex := 1,ifname := "wg0",peers :=
    ([0,1].foldl (fun peers id => peers.insert id {
      remoteStatic := List.replicate 32 0,presharedKey := List.replicate 32 0,
      precomputedStaticStatic := List.replicate 32 0,internalId := id}) ({} : Std.TreeMap PeerId Peer))}} }

def runCase (input : Input) (seed : UInt64) (family : Nat) : Except String Json := do
  let width := if family == 4 then 32 else 128
  let key (value : Nat) := value*2^(width-32)
  let yes (site : Nat) := record site true
  let no (site : Nat) := record site false
  let calls : List (String × Nat × Nat × Nat × List HiddenRecord) := [
    ("invalid-prefix",0,width+1,0,[]),
    ("empty-allocation-failure",key 0x0a000000,24,0,[no 7]),
    ("empty-root",key 0x0a000000,24,0,[yes 7]),
    ("exact-reassignment",key 0x0a000055,24,1,[]),
    ("first-child",key 0x0a000001,32,0,[yes 8]),
    ("other-child",key 0x0a000081,32,1,[yes 8]),
    ("covering-root",key 0x0a000000,16,0,[yes 8]),
    ("intermediate-root",key 0x0b000001,32,1,[yes 8,yes 9]),
    ("rollback",key 0x0c000001,32,0,[yes 8,no 9]),
    ("newnode-allocation-failure",key 0x0d000001,32,0,[no 8]),
    ("intermediate-becomes-peer",key 0x0a000000,7,0,[]),
    ("intermediate-child-and-reuse",key 0x0a000040,32,0,[yes 8,yes 9])]
  let mut s ← fixture input initialWorld
  let mut reports := #[]
  for (label,address,cidr,pid,records) in calls do
    let (after,report) ← (invoke input seed s family address cidr pid records).mapError
      (fun e => s!"{label}/family-{family}/seed-{seed}: {e}")
    let (afterLookup,look) ← (lookup input seed after family address).mapError
      (fun e => s!"lookup-after-{label}/family-{family}: {e}")
    reports := reports.push (Json.mkObj [("case",toJson label),("insert",report),("lookup",look)])
    s := afterLookup
  if family == 6 then
    for low in [1,2,0xffffffffffffffff] do
      let address := key 0x0a000001+low
      let records := if low == 1 then [yes 8] else [yes 8,yes 9]
      let (after,report) ← (invoke input seed s family address 128 1 records).mapError
        (fun e => s!"ipv6-low-word/{low}: {e}")
      let (afterLookup,look) ← lookup input seed after family address
      reports := reports.push (Json.mkObj [("case",toJson "ipv6-low-word"),("insert",report),("lookup",look)])
      s := afterLookup
  return Json.mkObj [("family",toJson family),("seed",toJson seed.toNat),("calls",toJson reports)]

def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "usage: binary-allowedips-mutation INPUT.json"; return 1
  let input ← liftE (Json.parse (← IO.FS.readFile path) >>= fromJson? (α := Input))
  for seed in [(0 : UInt64),0xffffffffffffffff] do
    for family in [4,6] do
      match runCase input seed family with
      | .error e => IO.eprintln s!"FAIL: {e}"; return 1
      | .ok report => IO.println report.compress
  IO.println "PASS: constructed insertion/lookup sequences; generic allocation/free returns supplied"
  return 0
