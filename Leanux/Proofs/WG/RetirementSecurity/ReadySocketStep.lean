import Leanux.Proofs.WG.RetirementSecurity.ReadySocketBody

/-! Exact cached peek obtains the queued readiness predicate. The same
completion observer carries it to each actual socket receipt, even when the
worker later stops. No ready-byte invariant is assumed at socket reads. -/
namespace Leanux.Proofs.WG.RetirementSecurity.ReadySocket
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity Completion ReadyCiphertext

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

def Selected (first : Option (List SkbId)) (h : List Completion.Event) (w : World) : Prop :=
  Good h ∧ ∀items,first=some items→ReadyHead items w.wg

theorem peek_safe (pid : PeerId) :
    PrefixEnsures (Inv ReadyCiphertext.Inv) Good (peek pid) Selected := by
  intro w h before
  obtain ⟨suffix,extension⟩:=peek_appends pid w h
  have good:Good (runPrefix (peek pid) w h).2:=by unfold Good; rw [peek_history pid w h]; exact before.2
  refine ⟨suffix,extension,good,?_⟩
  cases result:(runPrefix (peek pid) w h).1 with
  | error stop=>trivial
  | ok out=>
    refine ⟨good,?_⟩
    intro items selected
    have run:=(peek_erases pid w h).symm.trans result
    rw [liftWG_run] at run
    cases native:((txPeekSource pid).run w.wg).run w.ambient with
    | error stop=>simp [native,Except.map] at run
    | ok output=>
      obtain ⟨⟨first,v⟩,b⟩:=output
      simp only [native,Except.map,Except.ok.injEq] at run
      cases run
      change first=some items at selected
      obtain ⟨d,p,q,device,found,contents,cached,after⟩:=txPeek_effect pid w.ambient b native
      have member:items∈p.txQueue.all:=by rw [←contents]; simp [PrevQueue.all,cached,selected]
      have cells:TxDisposition.txPackets v=TxDisposition.txPackets w.wg:=by
        funext id; simp [TxDisposition.txPackets,after,replacePeer,device]
      intro headId head crypted
      have oldHead:TxDisposition.HeadState headId .crypted w.wg:=by
        obtain ⟨packet,stored,mark⟩:=crypted
        exact ⟨packet,cells ▸ stored,mark⟩
      exact Complete.cells (before.1 pid p (by simp [peerAt,device,found]) items member headId head oldHead) cells

theorem body_none (pid : PeerId) :
    PrefixEnsures (Inv (ReadyHead [])) Good (Completion.body pid none) (fun _ h _=>Good h) := by
  unfold Completion.body
  apply PrefixEnsures.bind (show PrefixEnsures (Inv (ReadyHead [])) Good (check none)
    (fun _=>Inv (ReadyHead [])) from check_safe none)
  intro go
  cases go with
  | false=>exact PrefixEnsures.pure (fun _ _ before=>before.2) (fun _ _ before=>before.2)
  | true=>
    apply (show PrefixEnsures (Inv (ReadyHead [])) Good
      (liftPrefix (liftWG (invariant "unreachable" : WG.M Bool)))
      (fun _=>Inv (ReadyHead [])) from stop "unreachable").consequence
    · intro _ _ before; exact before
    · intro _ _ _ after; exact after.2

theorem step_good (pid : PeerId) :
    PrefixEnsures (Inv ReadyCiphertext.Inv) Good (Completion.step pid) (fun _ h _=>Good h) := by
  have factor:Completion.step pid=(peek pid >>= Completion.body pid):=by
    simp only [Completion.step,peek,bind_assoc,pure_bind]
  rw [factor]
  apply PrefixEnsures.bind (peek_safe pid)
  intro first
  cases first with
  | none=>
    apply (body_none pid).consequence
    · intro h w before
      exact ⟨(by intro id head; cases head),before.1⟩
    · intro _ _ _ after; exact after
  | some items=>
    apply (body_some pid items).consequence
    · intro h w before
      exact ⟨before.2 items rfl,before.1⟩
    · intro _ _ _ after; exact after

theorem step (pid : PeerId) : PrefixPreserves (Inv ReadyCiphertext.Inv) Good (Completion.step pid) := by
  intro w h before
  obtain ⟨suffix,extension,good,_⟩:=step_good pid w h before
  refine ⟨suffix,extension,good,?_⟩
  cases run:(runPrefix (Completion.step pid) w h).1 with
  | error stop=>trivial
  | ok out=>
    have native:=HolderPoll.native_receipt ((Completion.step_erases pid w h).symm.trans run)
    exact ⟨(hoare_iff_run_ambient _ _ _).mp (ReadyCiphertext.Tx.step_inv pid)
      w.wg _ out.1 out.2.wg _ before.1 native,good⟩

end Leanux.Proofs.WG.RetirementSecurity.ReadySocket
