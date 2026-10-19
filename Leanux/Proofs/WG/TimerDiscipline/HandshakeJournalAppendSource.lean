import Leanux.Proofs.WG.TimerDiscipline.HandshakeJournalClaims
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
open Leanux Leanux.WG Leanux.Proofs.Logged Origins
theorem session_appends (pid : PeerId) : StateAppends (session pid) := by
  intro g a h
  change ∃more,(runWGPrefix (session pid) g a h).2=h++more
  rw [session_exact]
  cases ((beginSession pid).run g).run a with
  | error stop => exact ⟨[],by simp⟩
  | ok out => exact ⟨[_],rfl⟩
theorem hook_appends (kind : HookJournal.Hook) (pid : PeerId) :
    StateAppends (hook kind pid) :=
  StateAppends.focus _ _ (HookJournal.observed kind pid)
theorem appends_true {α : Type} (action : Obs α) (appends : StateAppends action) :
    StatePrefixPreserves (fun _ _ _=>True) (fun _=>True) action := by
  intro g a h _
  obtain ⟨more,same⟩:=appends g a h
  refine ⟨more,same,True.intro,?_⟩
  cases (runPrefix (action.run g) a h).1 <;> trivial
theorem true_appends {α : Type} (action : Obs α)
    (preserves : StatePrefixPreserves (fun _ _ _=>True) (fun _=>True) action) :
    StateAppends action := by
  intro g a h
  obtain ⟨more,same,_,_⟩:=preserves g a h True.intro
  exact ⟨more,same⟩
macro "journal_appends" : tactic => `(tactic|
  repeat' first
    | (maintenance_head session; exact appends_true _ (session_appends _))
    | (maintenance_head hook; exact appends_true _ (hook_appends _ _))
    | (maintenance_head liftWGPrefix; exact appends_true _ (StateAppends.lift _))
    | (maintenance_head Pure.pure; exact appends_true _ (StateAppends.pure _))
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q:=fun _ _ _ _=>True))
    | maintenance_intro
    | maintenance_join_let
    | maintenance_join_use
    | (maintenance_head ite;split)
    | (maintenance_head dite;split)
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_match
    | contradiction)
theorem response_appends (pid : PeerId) : StateAppends (response pid) := by
  apply true_appends
  unfold response HandshakeSources.responseWith
  dsimp (config:={zeta:=false}) only [ops]
  change StatePrefixEnsures _ _ _ (fun _ _ _ _=>True)
  journal_appends
theorem afterMac_appends (msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState) :
    StateAppends (afterMac msg src loaded mac) := by
  apply true_appends
  unfold afterMac HandshakeSources.afterMacWith HandshakeSources.responseWith
  dsimp (config:={zeta:=false}) only [ops]
  change StatePrefixEnsures _ _ _ (fun _ _ _ _=>True)
  journal_appends
theorem reception_appends (msg : List UInt8) (src : SkbSource) :
    StateAppends (reception msg src) := by
  unfold reception HandshakeSources.receptionWith
  apply StateAppends.bind (StateAppends.lift _)
  intro cookie
  split
  · exact StateAppends.bind (StateAppends.lift _) (fun _=>StateAppends.pure _)
  · apply StateAppends.bind (StateAppends.lift _)
    intro loaded
    apply StateAppends.bind (StateAppends.lift _)
    intro mac
    exact afterMac_appends msg src loaded mac
theorem step_appends : StateAppends step := by
  unfold step HandshakeSources.stepWith
  apply StateAppends.bind (StateAppends.lift _)
  intro d
  cases d.handshakeQueue.consume with
  | mk packet ring =>
    cases packet with
    | none => exact StateAppends.bind (StateAppends.lift _) (fun _=>StateAppends.pure _)
    | some packet =>
      obtain ⟨msg,src⟩:=packet
      apply StateAppends.bind (StateAppends.lift _)
      intro _
      apply StateAppends.bind (StateAppends.lift _)
      intro _
      apply StateAppends.bind (reception_appends msg src)
      intro _
      exact StateAppends.bind (StateAppends.lift _) (fun _=>StateAppends.pure _)
end Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
