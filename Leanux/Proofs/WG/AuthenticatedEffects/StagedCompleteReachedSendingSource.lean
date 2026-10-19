import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCuts
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteSend

/-! Fixed native source prefix ending immediately after the actual socket
result, before byte accounting. Unsupported families follow their original
counterless branch; this factor introduces no guard or synthetic source cut. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Sending
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open AllocatedObligation CompletionBatch CompletionFirstTerminal

def familySocket (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) : PrefixM Completion.Event Int := do
  let family := (peer.value.endpoint.map (·.family)).getD 0
  if ← liftPrefix (liftWG (branch .sendSkbInet (family == AF_INET))) then
    Completion.socket pid skb packet peer true
  else if ← liftPrefix (liftWG (branch .sendSkbInet6 (family == AF_INET6))) then
    Completion.socket pid skb packet peer false
  else pure (-EAFNOSUPPORT)

def beforeAccounting (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket) :
    PrefixM Completion.Event Int := do
  let peer ← captureObserved (Completion.access (getPeerMixed pid))
  familySocket pid skb packet peer

def accountingPrefix (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket) :
    PrefixM CausalJournal.Event Int := FirstTerminal.focused (beforeAccounting pid skb packet)

theorem send_factor (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket) :
    Completion.send pid skb packet = beforeAccounting pid skb packet >>= afterSocket pid packet := by
  rw [CompletionFirstTerminal.send_factor]
  unfold beforeAccounting
  rw [bind_assoc]
  congr 1
  funext peer
  simp only [CompletionFirstTerminal.afterPeer,familySocket,bind_assoc]
  congr 1
  funext flag
  cases flag with
  | true => rfl
  | false =>
    simp only [Bool.false_eq_true,↓reduceIte,bind_assoc]
    congr 1
    funext second
    cases second <;> rfl

theorem family_appends (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) : Appends (familySocket pid skb packet peer) := by
  unfold familySocket Completion.socket receiptObserved
  repeat' first
    | with_reducible exact Appends.lift _
    | with_reducible exact Appends.pure _
    | (change Appends (focusPrefix _ _ _); exact Appends.focus _ _ _)
    | (change Appends (emitPrefix _); exact fun _ _ => ⟨[_],rfl⟩)
    | with_reducible apply Appends.captureObserved
    | with_reducible apply Appends.bind
    | (with_reducible intro x; try dsimp only)
    | dsimp (config := {failIfUnchanged := true}) only
    | split

theorem before_appends (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket) :
    Appends (beforeAccounting pid skb packet) :=
  Appends.bind (Appends.captureObserved (Appends.focus _ _ _)) (family_appends pid skb packet)

theorem focused_factor (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket) :
    FirstTerminal.focused (Completion.send pid skb packet) =
      (accountingPrefix pid skb packet >>= fun ret => FirstTerminal.focused (afterSocket pid packet ret)) := by
  rw [send_factor]
  funext w history
  exact (focusPrefix_bind_appends FirstTerminal.encode CausalJournal.completion?
    (by intro event; cases event <;> rfl) (before_appends pid skb packet)
    (afterSocket_appends pid packet) w history).symm

theorem outer_failed (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket)
    (cut : runPrefix (accountingPrefix pid skb packet) w history = (.ok (ret,v),journal))
    (failed : runPrefix (FirstTerminal.focused (afterSocket pid packet ret)) v journal = (.error reason,last)) :
    runPrefix (CausalJournal.completionOps.send pid skb packet) w history = (.error reason,last) := by
  apply HandshakeSecurity.StagedConservation.SendResult.observed_stopped
  change runPrefix (FirstTerminal.focused (Completion.send pid skb packet)) w history = _
  rw [focused_factor,runPrefix_bind,cut]
  exact failed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Sending
