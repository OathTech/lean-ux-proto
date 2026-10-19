import SourceAdapter
import MirrorHistory

namespace Binary.MirrorHistory
open Leanux Leanux.WG
open LookupMirror (record)
open PeerMirror (recordCmp countRecords peerFinal)

def countPoints (w : World) (old : Nat) : List Point :=
  let z := recordCmp w .refcountAddNzZero (old == 0) old 0
  let r := if old == 0 then z else record z .refcountAddNzRetry false
  let n := record r .refcountAddNzNegative false
  [⟨.decision .refcountAddNzZero, z⟩] ++
    (if old == 0 then [] else [⟨.decision .refcountAddNzRetry, r⟩]) ++
    [⟨.decision .refcountAddNzNegative, n⟩,
     ⟨.decision .refcountAddNzWraps, countRecords w old⟩]

/-- Every decision World precedes the peer update, including the live
    dead=false point. Only the returned World contains the increment. -/
def peerPoints (w : World) (peer : Peer) : List Point :=
  let n := record w .peerGetMaybeZeroNull false
  let c := countRecords n peer.refcount
  let d := record c .peerGetMaybeZeroDead (peer.refcount == 0)
  [⟨.decision .peerGetMaybeZeroNull, n⟩] ++
    countPoints n peer.refcount ++ [⟨.decision .peerGetMaybeZeroDead, d⟩]

theorem count_run_logged (old : Nat) (h : List Point) (w : World)
    (small : old + 1 < 2^31) :
    ((count old).run h).run w =
      .ok ((old != 0, h ++ countPoints w old), countRecords w old) := by
  have noWrap : ¬old + 1 ≥ 2^31 := by omega
  by_cases zero : old = 0 <;>
    simp [Except.pure, Except.bind, StateT.run, bind, StateT.bind, StateT.lift, pure, StateT.pure, get, getThe, MonadStateOf.get, StateT.get, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, monadLift, MonadLift.monadLift, liftAmbient, AmbientM.branch, AmbientM.branchCmp,  count, branchCmpLogged, branchLogged, mark,
      branchCmp, branch, countPoints, countRecords,
      recordCmp, record, zero, noWrap, List.append_assoc] <;> rfl

theorem peer_null_run_logged (h : List Point) (w : World) :
    ((peerGet none).run h).run w =
      let n := record w .peerGetMaybeZeroNull true
      .ok ((none, h ++ [⟨.decision .peerGetMaybeZeroNull, n⟩]), n) := by
  rfl

theorem peer_run_logged (pid : PeerId) (h : List Point) (w : World)
    (device : Device) (peer : Peer)
    (hasDevice : w.wg.dev = some device)
    (hasPeer : device.peers.get? pid = some peer)
    (small : peer.refcount + 1 < 2^31) :
    ((peerGet (some pid)).run h).run w =
      .ok (((if peer.refcount = 0 then none else some pid),
        h ++ peerPoints w peer), peerFinal pid w peer) := by
  have peerRead : device.peers[pid]? = some peer := hasPeer
  have noWrap : ¬2147483647 ≤ peer.refcount := by omega
  by_cases zero : peer.refcount = 0
  all_goals have boolZero : (peer.refcount == 0) = decide (peer.refcount = 0) := rfl
  all_goals simp only [zero, decide_true, decide_false] at boolZero
  all_goals
    simp [Except.pure, Except.bind, StateT.run, bind, StateT.bind, StateT.lift, pure, StateT.pure, get, getThe, MonadStateOf.get, StateT.get, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, monadLift, MonadLift.monadLift, liftAmbient, AmbientM.branch, AmbientM.branchCmp,  liftWG, WG.requireNotPending, WG.getPeer, WG.getDev, WG.setPeer,   WG.modifyDev, peerGet, count, branchLogged, branchCmpLogged, mark,
      branch, branchCmp, Source.requireNotPending, Source.getPeer,
      hasDevice, peerRead, zero, noWrap, Source.setPeer,
      peerPoints, countPoints, peerFinal, countRecords,
      recordCmp, record, bne, boolZero, List.append_assoc] <;> rfl

theorem countPoints_kernel (w : World) (old : Nat) (q : Point)
    (member : q ∈ countPoints w old) : q.world.wg = w.wg := by
  by_cases zero : old = 0 <;>
    simp [countPoints, countRecords, recordCmp, record, zero] at member <;>
    rcases member with rfl | rfl | rfl | rfl <;> rfl

theorem peerPoints_kernel (w : World) (peer : Peer) (q : Point)
    (member : q ∈ peerPoints w peer) : q.world.wg = w.wg := by
  simp only [peerPoints, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (rfl | member) | rfl
  · rfl
  · exact countPoints_kernel (record w .peerGetMaybeZeroNull false) peer.refcount q member
  · simp only [countRecords, record, recordCmp]
    split <;> rfl

/-- Call/return marks use the actual incoming/final Worlds. The intermediate
    points are the exact logged run established by the action's equation. -/
theorem called_run (symbol : String) (action : Logged α)
    (w w' : World) (answer : α) (points : List Point)
    (run : ∀ h, (action.run h).run w = .ok ((answer, h ++ points), w'))
    (h : List Point) :
    ((called symbol action).run h).run w =
      .ok ((answer, h ++ [⟨.call symbol, w⟩] ++ points ++
        [⟨.returned symbol, w'⟩]), w') := by
  simp [called, mark, StateT.run_bind, run, List.append_assoc]
  rfl


#print axioms called_run

#print axioms count_run_logged
#print axioms peer_null_run_logged
#print axioms peer_run_logged
#print axioms countPoints_kernel
#print axioms peerPoints_kernel
end Binary.MirrorHistory
