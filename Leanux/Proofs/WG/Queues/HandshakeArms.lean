import Leanux.Proofs.WG.Queues.HandshakeInitiation

/-! The source's absent acquisition returns normally before final payment.
Only selected peers reach the shared statistics/timer/payment continuation. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HandshakeArms
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders HandshakeResponse

def complete (peer : Option PeerId) (msg : List UInt8) : WG.M Unit :=
  match peer with
  | none => pure ()
  | some _ => HandshakeReceive.finishSelected peer msg

theorem complete_spec (peer : Option PeerId) (msg : List UInt8) :
    Hoare (complete peer msg) (Selected cs loans peer) (fun _ => Boundary cs loans) := by
  cases peer with
  | none => exact preserves_pure ()
  | some pid => exact HandshakeResponse.finish (some pid) msg

def initiation (msg : List UInt8) (src : SkbSource) : WG.M Unit := do
  let peer ← consumeInitiation msg
  if ← branch .hsInitNoPeer peer.isNone then return
  let some pid := peer | invariant "unreachable"
  setPeerEndpointFromSkb pid src
  sendHandshakeResponse pid
  HandshakeReceive.finishSelected peer msg

def response (msg : List UInt8) (src : SkbSource) : WG.M Unit := do
  let peer ← consumeResponse msg
  if ← branch .hsRespNoPeer peer.isNone then return
  let some pid := peer | invariant "unreachable"
  setPeerEndpointFromSkb pid src
  HandshakeReceive.responseSession pid
  HandshakeReceive.finishSelected peer msg

theorem initiation_factor (msg : List UInt8) (src : SkbSource) :
    initiation msg src = (HandshakeInitiation.branchSource msg src >>= fun peer => complete peer msg) := by
  unfold initiation HandshakeInitiation.branchSource HandshakeInitiation.afterLookup
  simp only [bind_assoc]
  apply congrArg (Bind.bind (consumeInitiation msg))
  funext peer
  apply congrArg (Bind.bind (branch .hsInitNoPeer peer.isNone : WG.M Bool))
  funext missing
  cases missing <;> cases peer
  all_goals first
    | rfl
    | simp only [Bool.false_eq_true,ite_false,bind_assoc,pure_bind,complete]

theorem response_factor (msg : List UInt8) (src : SkbSource) :
    response msg src = (HandshakeResponse.branchSource msg src >>= fun peer => complete peer msg) := by
  unfold response HandshakeResponse.branchSource HandshakeResponse.afterLookup
  simp only [bind_assoc]
  apply congrArg (Bind.bind (consumeResponse msg))
  funext peer
  apply congrArg (Bind.bind (branch .hsRespNoPeer peer.isNone : WG.M Bool))
  funext missing
  cases missing <;> cases peer
  all_goals first
    | rfl
    | simp only [Bool.false_eq_true,ite_false,bind_assoc,pure_bind,complete]

theorem initiation_spec (msg : List UInt8) (src : SkbSource) :
    Hoare (initiation msg src) (Input cs loans) (fun _ => Boundary cs loans) := by
  rw [initiation_factor]
  exact hoare_bind _ _ (HandshakeInitiation.branch_spec msg src) (fun peer => complete_spec peer msg)

theorem response_spec (msg : List UInt8) (src : SkbSource) :
    Hoare (response msg src) (Input cs loans) (fun _ => Boundary cs loans) := by
  rw [response_factor]
  exact hoare_bind _ _ (HandshakeResponse.branch_spec msg src) (fun peer => complete_spec peer msg)

end Leanux.Proofs.WG.Queues.RxCredits.HandshakeArms
