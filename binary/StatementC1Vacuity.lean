import StatementC1Headline

/-! Result C1, final statement: the kernel-checked evidence against vacuity that
the result carries, as statements (no theorem, no proof), and `Signed`. `Witness` says the
premises can be met along an actual execution through every kind of call;
the two exclusions are consequences with no mirror state in their
conclusion, naming machine behaviours the headline rules out. -/
namespace Binary.Statements.C1
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage
local instance : Labels := Image.linkedLabels

/-- An actual finite execution from `s` that ends at `t`, returned to `ra`. -/
def Ran (fetch : Int64 → Option Decoded) (s t : MachineState) (ra : UInt64)
    (history : List MachineState) : Prop :=
  ActualHistory fetch s history ∧ history.getLast? = some t ∧ Returned s t ra

def HeapSame (L : Layout) (t s : MachineState) : Prop :=
  ∀ a, L.Heap a → t.data.dmem.get? a = s.data.dmem.get? a

def outcome (site : Nat) (ok : Bool) : HiddenRecord := ⟨site, (if ok then 1 else 0) :: List.replicate 39 0⟩

/-- WITNESS (revision 2). Some `fetch`, layout and allocator meet every
premise, and an actual execution runs, from a physically empty table with
the allocator idle and five answers pending, through: an insertion into the
empty table; an insertion that allocates twice (the intermediate node,
while a node is handed out); an insertion whose second allocation is
refused (the rollback and the release); and a lookup that finds a peer.
Each call meets its caller conditions and the mirror accepts it, consuming
exactly those records. The code at `allocEntry` uses a nonempty stack
scratch and, with the coverage buffer in use, changes a scratch byte and a
buffer byte during the second call's allocation. The service will be a
stub and is to be called one. -/
def Witness : Prop :=
  ∃ (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator)
    (w0 w1 w2 w3 w4 : World) (d0 d3 : Device) (c1 c2 c3 c4 : Context)
    (s1 t1 s2 t2 s3 t3 s4 t4 : MachineState) (h1 h2 h3 h4 : List MachineState)
    (k1 n1 p1 k2 n2 p2 k3 n3 p3 key pointer : Nat) (found : PeerId) (ra : UInt64)
    (stream : List HiddenRecord),
    Premises fetch L A ∧
    w0.wg.dev = some d0 ∧ armed w0 = true ∧
    w0.ambient.hidden = some ([outcome 77 true, outcome 78 true, outcome 79 true,
      outcome 78 true, outcome 79 false] ++ stream) ∧
    (∀ record ∈ stream, record.site ∈ allocSites.map (·.2)) ∧
    emptyTable L s1.data.dmem d0 = .ok () ∧
    A.Idle s1.data.dmem [] ([outcome 77 true, outcome 78 true, outcome 79 true,
      outcome 78 true, outcome 79 false] ++ stream) ∧
    insertReady L A c1 s1 4 k1 n1 p1 ra = .ok () ∧
    (liftWG (WG.insert 4 k1 n1 p1)).run w0 = .ok (0, w1) ∧ Ran fetch s1 t1 ra h1 ∧
    HeapSame L t1 s2 ∧ insertReady L A c2 s2 4 k2 n2 p2 ra = .ok () ∧
    (liftWG (WG.insert 4 k2 n2 p2)).run w1 = .ok (0, w2) ∧
    w2.ambient.hidden = some ([outcome 78 true, outcome 79 false] ++ stream) ∧ Ran fetch s2 t2 ra h2 ∧
    HeapSame L t2 s3 ∧ insertReady L A c3 s3 4 k3 n3 p3 ra = .ok () ∧
    (liftWG (WG.insert 4 k3 n3 p3)).run w2 = .ok (-12, w3) ∧
    w3.ambient.hidden = some stream ∧ Ran fetch s3 t3 ra h3 ∧
    HeapSame L t3 s4 ∧ lookupReady L c4 s4 4 key ra = .ok () ∧ w3.wg.dev = some d3 ∧
    (Source.lookup d3.peerAllowedips.root4 32 key).run w3 = .ok (some found, w4) ∧
    Trie.address L.peers (some found) = .ok pointer ∧ Ran fetch s4 t4 ra h4 ∧
    0 < A.depth ∧ c2.Needed ∧
    ∃ (enter leave : MachineState) (back : UInt64), enter ∈ h2 ∧ leave ∈ h2 ∧
      enter.pc = allocEntry ∧ Returned enter leave back ∧
      (∃ a, Scratch enter A.depth a ∧ enter.data.dmem.get? a ≠ leave.data.dmem.get? a) ∧
      (∃ a, c2.writes a ∧ enter.data.dmem.get? a ≠ leave.data.dmem.get? a)

/-- The caller's conditions for a lookup of `key` in any state that agrees
with `t` on the heap. -/
def LookupAfter (L : Layout) (t s : MachineState) (c : Context) (family key : Nat) (ra : UInt64) : Prop :=
  HeapSame L t s ∧ lookupReady L c s family key ra = .ok ()

/-- The mirror accepts the insertion and then a lookup of the same address
(it refuses a lookup that would retry on a dying peer). The exclusions take
this as a hypothesis and mention no mirror state in their conclusions. -/
def MirrorAccepts (w : World) (family key cidr pid : Nat) : Prop :=
  ∃ answer w' d' found w'', (liftWG (WG.insert family key cidr pid)).run w = .ok (answer, w') ∧
    w'.wg.dev = some d' ∧
    (Source.lookup (if family == 4 then d'.peerAllowedips.root4 else d'.peerAllowedips.root6)
      (if family == 4 then 32 else 128) key).run w' = .ok (found, w'')

/-- EXCLUSION 1 (a route is not lost). At a physically empty table whose
allocator will succeed, an insertion of `key/cidr` with a prefix length in
range returns 0, and every later lookup of `key` returns that peer's
address, which is not NULL. -/
def InsertThenLookup : Prop :=
  ∀ (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator), Premises fetch L A →
  ∀ (w : World) (d : Device) (c : Context) (s : MachineState) (family key cidr pid peer : Nat)
    (ra : UInt64) (stream : List HiddenRecord),
    w.wg.dev = some d → armed w = true →
    w.ambient.hidden = some (⟨77, 1 :: List.replicate 39 0⟩ :: stream) →
    (∀ record ∈ stream, record.site ∈ allocSites.map (·.2)) →
    emptyTable L s.data.dmem d = .ok () →
    A.Idle s.data.dmem [] (⟨77, 1 :: List.replicate 39 0⟩ :: stream) →
    insertReady L A c s family key cidr pid ra = .ok () →
    cidr ≤ (if family = 4 then 32 else 128) →
    Trie.address L.peers (some pid) = .ok peer →
    MirrorAccepts w family key cidr pid →
    Eventually (instructionStep fetch) (fun t =>
      Returned s t ra ∧ t.data.regs.get (.low .rax .W32) = 0#32 ∧
      ∀ (s' : MachineState) (c' : Context) (ra' : UInt64), LookupAfter L t s' c' family key ra' →
        Eventually (instructionStep fetch) (fun t' =>
          Returned s' t' ra' ∧ t'.data.regs.rax.toNat = peer ∧ peer ≠ 0) s') s

/-- EXCLUSION 2 (a failed insertion is invisible). At a physically empty
table whose allocator will refuse, the insertion returns `-ENOMEM` and
every later lookup of `key` returns NULL. -/
def FailedInsertInvisible : Prop :=
  ∀ (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator), Premises fetch L A →
  ∀ (w : World) (d : Device) (c : Context) (s : MachineState) (family key cidr pid : Nat)
    (ra : UInt64) (stream : List HiddenRecord),
    w.wg.dev = some d → armed w = true →
    w.ambient.hidden = some (⟨77, 0 :: List.replicate 39 0⟩ :: stream) →
    (∀ record ∈ stream, record.site ∈ allocSites.map (·.2)) →
    emptyTable L s.data.dmem d = .ok () →
    A.Idle s.data.dmem [] (⟨77, 0 :: List.replicate 39 0⟩ :: stream) →
    insertReady L A c s family key cidr pid ra = .ok () →
    cidr ≤ (if family = 4 then 32 else 128) →
    MirrorAccepts w family key cidr pid →
    Eventually (instructionStep fetch) (fun t =>
      Returned s t ra ∧ t.data.regs.get (.low .rax .W32) = BitVec.ofInt 32 (-12) ∧
      ∀ (s' : MachineState) (c' : Context) (ra' : UInt64), LookupAfter L t s' c' family key ra' →
        Eventually (instructionStep fetch) (fun t' =>
          Returned s' t' ra' ∧ t'.data.regs.rax.toNat = 0) s') s

/-- WHAT IS SIGNED (revision 2): the headline together with the evidence
against vacuity it relies on. The exclusions follow from `Headline` and
facts about the mirror; the witness is independent of it. -/
def Signed : Prop :=
  Headline ∧ Witness ∧ InsertThenLookup ∧ FailedInsertInvisible

end Binary.Statements.C1
