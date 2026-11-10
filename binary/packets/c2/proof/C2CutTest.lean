import C2Cut
import Leanux.Runner

/-! Executed test of the cut's pivot (`Binary.C2.validate`, `toCounter`, `ofCounter`,
`exitPC`) against the mirror's `counterValidate`: on every case below the mirror's
result, the replay state it leaves and the exit the statement names are the pivot's.
This is a speedbump against a wrong pivot, not a proof: `MirrorFollowsSpec` is the
proposition. Run with `binary/packets/c2/proof/check`. In no lake target. -/
namespace Binary.C2.CutTest
open Binary TrustBase Leanux Binary.C2

def worldOf (rc : WG.ReplayCounter) : WGWorld :=
  let k : WG.Keypair := { peer := none, receivingCounter := rc }
  let ks : Std.TreeMap WG.KeypairId WG.Keypair := (∅ : Std.TreeMap WG.KeypairId WG.Keypair).insert 0 k
  let d : WG.Device := { ifindex := 3, ifname := "wg0", keypairs := ks }
  { dev := some d }

def ambient : Ambient := { env := Leanux.Runner.harnessEnv, timing := Leanux.Env.timing }

def mirror (rc : WG.ReplayCounter) (nonce : Nat) : Except String (Bool × WG.ReplayCounter) :=
  match ((WG.counterValidate 0 nonce).run (worldOf rc)).run ambient with
  | .error e => .error s!"mirror refused: {e.message}"
  | .ok ((result, world'), _) =>
    match windowOf world' 0 with
    | some rc' => .ok (result, rc')
    | none => .error "mirror lost the keypair"

def bitmap (seed : Nat) : Array Nat :=
  Array.ofFn (n := 128) fun j => (seed * 0x9e3779b97f4a7c15 + j.val * 0xa5a5a5a5a5a5a5a5 + seed * j.val) % 2 ^ 64

def top64 : Nat := 2 ^ 64

/-- Stored counters and packet counters around every boundary the range tests. -/
def counters : List Nat :=
  [0, 1, 62, 63, 64, 65, 127, 128, 8127, 8128, 8129, 8191, 8192, 8193, 16384, 100000,
   0xffffffffffffe03d - 8200, 0xffffffffffffe03d - 8129, 0xffffffffffffe03d - 64,
   0xffffffffffffe03c, 0xffffffffffffe03d, 0xffffffffffffe03e, 0xffffffffffffe03f,
   top64 - 2, top64 - 1]

def check (seed counter nonce : Nat) : Option String :=
  let rc : WG.ReplayCounter := { counter := counter, backtrack := bitmap seed }
  let o := validate (ofCounter rc) (.ofNat 64 nonce)
  match mirror rc nonce with
  | .error e => some s!"{counter} {nonce}: {e}"
  | .ok (result, rc') =>
    if result != o.accepted then some s!"{counter} {nonce}: accepted {o.accepted}, mirror {result}"
    else if rc'.counter != (toCounter o.window).counter || rc'.backtrack != (toCounter o.window).backtrack then
      some s!"{counter} {nonce}: window differs"
    else if o.exit != exitPC rc nonce then some s!"{counter} {nonce}: exit differs"
    else none

def failures : List String := Id.run do
  let mut out := []
  for seed in [0, 1, 7] do
    for counter in counters do
      for nonce in counters do
        if let some f := check seed counter nonce then out := f :: out
      -- a second visit of the same counter, and its neighbours
      for delta in [0, 1, 63, 64, 8127, 8128, 8129] do
        if let some f := check seed counter (counter + delta) then out := f :: out
        if let some f := check seed counter (counter - delta) then out := f :: out
  return out.reverse

#eval show IO Unit from do
  let fs := failures
  if fs.isEmpty then IO.println s!"C2CutTest: pivot agrees with the mirror on {3 * (counters.length * counters.length + counters.length * 14)} cases"
  else throw <| IO.userError s!"C2CutTest: {fs.length} failures, first: {fs.head!}"

end Binary.C2.CutTest
