import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTxSendFrontWorker

/-! Byte accounting uses the existing native access points, including the
saved peer write before its lifetime marker. The completion observer retains
the same journal projection as the shared lifetime-access observer. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxAccountingAccess
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation Prepare.Points
abbrev History := List CausalJournal.Event

def observed (body : MixedM α) : PrefixM CausalJournal.Event α :=
  FirstTerminal.focused (Completion.access body)

theorem observed_eq (body : MixedM α) : observed body=KeyAccess.observed body := by
  unfold observed FirstTerminal.focused Completion.access
  rw [CompletionEffects.focus_composed]
  have decode : (fun event=>(CausalJournal.completion? event).bind Completion.disposition?)=CausalJournal.txEvent? := by
    funext event
    cases event <;> first | rfl | (rename_i old; cases old <;> rfl)
  change focusPrefix CausalJournal.txEvent (fun event=>(CausalJournal.completion? event).bind Completion.disposition?)
    (TxDisposition.nativeAccess body)=_
  rw [decode]
  rfl

noncomputable def canonical (pid : PeerId) (size : Nat) :
    Shape (modifyPeerKeysPrefix pid fun p=>{p with txBytes:=p.txBytes+size}) := by
  unfold modifyPeerKeysPrefix getPeerMixed setPeerMixed peerStateFocus
  exact .bind (.focus _ _ (fun _=>rfl) (.access (.readPeer pid)))
    (fun p=>.focus _ _ (fun _=>rfl) (.access (.writePeer pid {p with txBytes:=p.txBytes+size})))

inductive RootPoint (pid : PeerId) (size : Nat) : World → History → World → History → Prop where
  | source {w : World} {h : History} {site : Site} {v : WGWorld} {b : Ambient}
      {middle : List LifetimeEvent} {remaining : MixedM Unit}
      (point : Point (canonical pid size) w.wg w.ambient (KeyAccess.project h) site v b middle remaining) :
      RootPoint pid size w h {w with wg:=v,ambient:=b}
        (h++(middle.drop (KeyAccess.project h).length).map KeyAccess.encode)

theorem RootPoint.remaining (point : RootPoint pid size w h u middle) :
    ∃remaining,runPrefix (observed (modifyPeerKeysPrefix pid fun p=>{p with txBytes:=p.txBytes+size})) w h=
      runPrefix remaining u middle := by
  cases point with
  | @source site v b middle remaining point=>
      obtain ⟨suffix,extended⟩:=point.appends
      refine ⟨KeyAccess.observed remaining,?_⟩
      rw [observed_eq,extended,List.drop_left]
      exact KeyAccess.observed_remainder _ _ _ _ _ _ suffix (by rw [←extended];exact point.run) point.remaining_appends

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxAccountingAccess
