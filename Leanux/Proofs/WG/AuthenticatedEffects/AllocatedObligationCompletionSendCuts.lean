import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionIndexedRefusal

/-! Source-level cuts join the same captured peer read to the actual family
branch and focused socket/accounting suffix. Defaults and source order are
unchanged, and the equalities retain every internal Stop prefix. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionSendCuts
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open CompletionFirstTerminal

def inet4World (w : World) : World :=
  {w with ambient := CounterWindow.record w.ambient .sendSkbInet true}

def inet6World (w : World) : World :=
  let first := CounterWindow.record w.ambient .sendSkbInet false
  {w with ambient := CounterWindow.record first .sendSkbInet6 true}

private theorem nativeBranch (w : World) (decision : Decision) (value : Bool) :
    (liftWG (branch decision value)).run w =
      .ok (value,{w with ambient := CounterWindow.record w.ambient decision value}) := rfl

theorem afterPeer4_run (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (w : World) (history : List Completion.Event)
    (family : (peer.value.endpoint.map (·.family)).getD 0 = AF_INET) :
    runPrefix (afterPeer pid skb packet peer) w history =
      runPrefix (Completion.socket pid skb packet peer true >>= afterSocket pid packet) (inet4World w) history := by
  simp [afterPeer,family,runPrefix_bind,runPrefix_lift,nativeBranch,inet4World]

theorem afterPeer6_run (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (w : World) (history : List Completion.Event)
    (not4 : (peer.value.endpoint.map (·.family)).getD 0 ≠ AF_INET)
    (family : (peer.value.endpoint.map (·.family)).getD 0 = AF_INET6) :
    runPrefix (afterPeer pid skb packet peer) w history =
      runPrefix (Completion.socket pid skb packet peer false >>= afterSocket pid packet) (inet6World w) history := by
  have is4 := beq_eq_false_iff_ne.mpr not4
  have is6 : ((peer.value.endpoint.map (·.family)).getD 0 == AF_INET6) = true := by rw [family]; rfl
  simp [afterPeer,is4,is6,runPrefix_bind,runPrefix_lift,nativeBranch,inet6World]

theorem afterPeer_appends (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) : Appends (afterPeer pid skb packet peer) := by
  unfold afterPeer Completion.socket receiptObserved afterSocket
  repeat' first
    | (change Appends (focusPrefix _ _ _); exact Appends.focus _ _ _)
    | with_reducible exact Appends.lift _
    | with_reducible exact Appends.pure _
    | (change Appends (emitPrefix _); exact fun _ _ => ⟨[_],rfl⟩)
    | with_reducible apply Appends.captureObserved
    | with_reducible apply Appends.bind
    | (with_reducible intro x; try dsimp only)
    | dsimp (config := {failIfUnchanged := true}) only
    | split

theorem focused_after_read (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (w u : World) (history : List CausalJournal.Event)
    (middle : List Completion.Event)
    (read : runPrefix (captureObserved (Completion.access (getPeerMixed pid))) w
      (history.filterMap CausalJournal.completion?) =
        (.ok (peer,u),history.filterMap CausalJournal.completion? ++ middle)) :
    runPrefix (FirstTerminal.focused (Completion.send pid skb packet)) w history =
      runPrefix (FirstTerminal.focused (afterPeer pid skb packet peer)) u
        (history ++ middle.map FirstTerminal.encode) := by
  have distribute := focusPrefix_bind_appends
    (a := captureObserved (Completion.access (getPeerMixed pid))) FirstTerminal.encode CausalJournal.completion?
    (by intro event; cases event <;> rfl)
    (Appends.captureObserved (Appends.focus _ _ _)) (afterPeer_appends pid skb packet) w history
  rw [send_factor]
  rw [← distribute,runPrefix_bind,
    focusPrefix_suffix FirstTerminal.encode CausalJournal.completion? _ w history (.ok (peer,u)) middle read]

theorem focused_family4 (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (w : World) (history : List CausalJournal.Event)
    (family : (peer.value.endpoint.map (·.family)).getD 0 = AF_INET) :
    runPrefix (FirstTerminal.focused (afterPeer pid skb packet peer)) w history =
      runPrefix (FirstTerminal.focused
        (Completion.socket pid skb packet peer true >>= afterSocket pid packet)) (inet4World w) history := by
  change ((runPrefix (afterPeer pid skb packet peer) w (history.filterMap CausalJournal.completion?)).1,
    history ++ List.map FirstTerminal.encode _) = _
  rw [afterPeer4_run pid skb packet peer w _ family]
  rfl

theorem focused_family6 (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (w : World) (history : List CausalJournal.Event)
    (not4 : (peer.value.endpoint.map (·.family)).getD 0 ≠ AF_INET)
    (family : (peer.value.endpoint.map (·.family)).getD 0 = AF_INET6) :
    runPrefix (FirstTerminal.focused (afterPeer pid skb packet peer)) w history =
      runPrefix (FirstTerminal.focused
        (Completion.socket pid skb packet peer false >>= afterSocket pid packet)) (inet6World w) history := by
  change ((runPrefix (afterPeer pid skb packet peer) w (history.filterMap CausalJournal.completion?)).1,
    history ++ List.map FirstTerminal.encode _) = _
  rw [afterPeer6_run pid skb packet peer w _ not4 family]
  rfl

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionSendCuts
