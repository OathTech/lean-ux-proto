import Leanux.Proofs.WG.TransmitSecurity.CompletionPeer
import Leanux.Proofs.WG.TransmitSecurity.CompletionPeerDisposal

/-! The original TX worker derives its selected batch alignment from the
actual cached peek. A normal or stopped completion retains peer-bound receipts. -/
namespace Leanux.Proofs.WG.TransmitSecurity.CompletionPeer
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity
set_option maxHeartbeats 600000

macro "completion_body_peer_step" : tactic => `(tactic| first
  | (nonce_product_head Completion.complete; exact CompletionPeer.complete _ _)
  | (nonce_product_head focusPrefix; first | with_reducible exact CompletionPeer.drop _ _ | with_reducible exact CompletionPeer.dispose _ _ _)
  | (nonce_product_head Completion.access; exact access (getTxSkbPrefix_erases _) (PacketMaterial.read_tx _))
  | (nonce_product_head liftPrefix; first | exact CompletionPeer.branch _ _ | exact CompletionPeer.stop _)
  | (nonce_product_head Pure.pure; exact PrefixPreserves.pure (fun _ _ hi => hi.2) _)
  | (nonce_product_head Bind.bind; apply PrefixPreserves.bind)
  | (nonce_product_head ite; apply PrefixPreserves.ite)
  | maintenance_intro
  | dsimp (config := {failIfUnchanged := true}) only
  | split)

theorem body_some (pid : PeerId) (items : List SkbId) :
    PrefixPreserves (Inv pid slot items) Good (Completion.body pid (some items)) := by
  unfold Completion.body TxDisposition.andObs
  cases items <;> simp only [Option.isSome_some,List.head?_nil,List.head?_cons]
  all_goals repeat' completion_body_peer_step

theorem body_none (pid : PeerId) :
    PrefixPreserves (Inv pid slot []) Good (Completion.body pid none) := by
  unfold Completion.body TxDisposition.andObs
  simp only [Option.isSome_none]
  repeat' completion_body_peer_step

def peek (pid : PeerId) : PrefixM Completion.Event (Option (List SkbId)) := do
  let p ← Completion.access (getPeerMixed pid)
  let (first,q) ← liftPrefix (liftWG p.txQueue.peek)
  Completion.access (modifyPeerKeysPrefix pid fun p => {p with txQueue := q})
  return first

theorem peek_erases (pid : PeerId) : ErasesPrefix (peek pid) (liftWG (txPeekSource pid)) := by
  unfold peek txPeekSource
  simp only [liftWG_bind,liftWG_pure]
  apply erasesPrefix_bind (Completion.access_erases (getPeerMixed_erases pid))
  intro peer
  apply erasesPrefix_bind (erasesPrefix_lift _)
  rintro ⟨first,q⟩
  simpa only [liftWG_bind,bind_assoc] using
    erasesPrefix_bind (Completion.access_erases (modifyPeerKeysPrefix_erases pid (fun p => {p with txQueue := q})))
      (fun _ => erasesPrefix_pure first)

private theorem peek_history (pid : PeerId) : HistoryFrame Completion.socket? (peek pid) := by
  unfold peek
  apply HistoryFrame.bind (focusPrefix_other _ _ _ (fun _ => rfl) _)
  intro peer
  apply HistoryFrame.bind (HistoryFrame.lift _ _)
  rintro ⟨first,q⟩
  apply HistoryFrame.bind (focusPrefix_other _ _ _ (fun _ => rfl) _)
  intro _
  exact HistoryFrame.pure _ _

private theorem peek_appends (pid : PeerId) : Appends (peek pid) := by
  unfold peek
  apply Appends.bind (Appends.focus _ _ _)
  intro peer
  apply Appends.bind (Appends.lift _)
  rintro ⟨first,q⟩
  exact Appends.bind (Appends.focus _ _ _) (fun _ => Appends.pure _)

def Selected (pid : PeerId) (first : Option (List SkbId))
    (h : List Completion.Event) (w : World) : Prop :=
  Good h ∧ ∀ items, first = some items → ∃ slot, BatchCoherence.Aligned w.wg pid slot items

theorem peek_safe (pid : PeerId) :
    PrefixEnsures (fun h (w : World) => BatchCoherence.Inv w.wg ∧ Good h) Good (peek pid)
      (Selected pid) := by
  intro w h before
  obtain ⟨suffix,extension⟩ := peek_appends pid w h
  have good : Good (runPrefix (peek pid) w h).2 := by
    unfold Good
    rw [peek_history pid w h]
    exact before.2
  refine ⟨suffix,extension,good,?_⟩
  cases result : (runPrefix (peek pid) w h).1 with
  | error stop => trivial
  | ok out =>
    refine ⟨good,?_⟩
    intro items selected
    have run := (peek_erases pid w h).symm.trans result
    rw [liftWG_run] at run
    cases native : ((txPeekSource pid).run w.wg).run w.ambient with
    | error stop => simp [native,Except.map] at run
    | ok output =>
      obtain ⟨⟨first,v⟩,b⟩ := output
      simp only [native,Except.map,Except.ok.injEq] at run
      cases run
      change first = some items at selected
      obtain ⟨d,p,q,device,found,contents,cached,after⟩ := txPeek_effect pid w.ambient b native
      have member : items ∈ p.txQueue.all := by
        rw [← contents]
        simp [PrevQueue.all,cached,selected]
      obtain ⟨slot,aligned⟩ := before.1 pid p (by simp [peerAt,device,found]) items member
      refine ⟨slot,?_⟩
      apply aligned.frame
      funext id
      simp [PacketMaterial.view,TxDisposition.txPackets,after,replacePeer,device]

theorem step (pid : PeerId) :
    PrefixEnsures (fun h (w : World) => BatchCoherence.Inv w.wg ∧ Good h) Good
      (Completion.step pid) (fun _ h _ => Good h) := by
  have factor : Completion.step pid = (peek pid >>= Completion.body pid) := by
    simp only [Completion.step,peek,bind_assoc,pure_bind]
  rw [factor]
  apply PrefixEnsures.bind (peek_safe pid)
  intro first w h before
  cases first with
  | none =>
    obtain ⟨suffix,extension,good,_⟩ := body_none (slot := 0) pid w h
      ⟨(by intro id member; cases member),before.1⟩
    exact ⟨suffix,extension,good,by cases (runPrefix (Completion.body pid none) w h).1 <;> trivial⟩
  | some items =>
    obtain ⟨slot,aligned⟩ := before.2 items rfl
    obtain ⟨suffix,extension,good,_⟩ := body_some (slot := slot) pid items w h ⟨aligned,before.1⟩
    exact ⟨suffix,extension,good,by cases (runPrefix (Completion.body pid (some items)) w h).1 <;> trivial⟩

end Leanux.Proofs.WG.TransmitSecurity.CompletionPeer
