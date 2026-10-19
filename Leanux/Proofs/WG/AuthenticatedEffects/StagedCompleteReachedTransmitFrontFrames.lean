import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTransmitFrontSource

/-! Native guard-prefix frames retain the incoming fixed ledger on each
actual normal return. These rules do not create a returned world on Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Transmit.Front
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open TransmitSecurity TransmitSecurity.Staged.Obligations CausalJournal CompleteCarrier Lifetimes Queues
set_option maxHeartbeats 600000

/-- The native queue, material and physical frames are joined for the very
same run, rather than choosing a second accounting endpoint. -/
theorem native_account {action : WG.M α}
    (queues : Preserves (QueueInv h ledger) action)
    (material : SameView StagedAdmission.Front.Material.view action)
    (ownership : SameView StagedAdmission.Front.Ownership.view action)
    (before : Accounted h ledger debts locals w)
    (run : (action.run w).run a=.ok ((value,v),b)) : Accounted h ledger debts locals v := by
  have fields := (ProjectedAction.iff_run_ambient _ _ _).mp material w a value v b run
  have owned := CompleteFront.physical before.entry
    ((ProjectedAction.iff_run_ambient _ _ _).mp ownership w a value v b run)
  exact ⟨⟨⟨before.entry.core.valid,
    (hoare_iff_run_ambient _ _ _).mp queues w a value v b before.entry.core.queues run,
    before.entry.core.selected,before.entry.core.physical.views (congrArg Prod.fst fields) (congrArg Prod.snd fields)⟩,
    before.entry.justified,before.entry.allocationLinks,before.entry.noSelected,
    owned.1,owned.2.1,owned.2.2⟩,before.complete⟩

theorem check_account (input : Input) (before : Accounted h ledger debts locals w)
    (run : ((Packets.txCheck input.family input.address input.packets input.mtu).run w).run a=
      .ok ((value,v),b)) : Accounted h ledger debts locals v :=
  native_account (StagedAdmission.Front.Native.check _ _ _ _)
    (StagedAdmission.Front.Material.check _ _ _ _) (StagedAdmission.Front.Ownership.check _ _ _ _) before run

theorem lookup_account (input : Input) (before : Accounted h ledger debts locals w)
    (run : ((lookupDst input.family input.address).run w).run a=.ok ((value,v),b)) :
    Accounted h ledger debts locals v :=
  native_account (StagedAdmission.Front.Native.lookup _ _)
    (StagedAdmission.Front.Material.lookup _ _) (StagedAdmission.Front.Ownership.lookup _ _) before run

theorem error_account (input : Input) (code : Int) (before : Accounted h ledger debts locals w)
    (run : ((Packets.txError input.family (input.packets.head?.getD {bytes := []}) code).run w).run a=
      .ok ((value,v),b)) : Accounted h ledger debts locals v :=
  native_account (StagedAdmission.Front.Native.error _ _ _)
    (StagedAdmission.Front.Material.error _ _ _) (StagedAdmission.Front.Ownership.error _ _ _) before run

theorem choose_checked (input : Input) (peer : Option PeerId) :
    CompleteCarrier.Checked ledger debts locals (choose input peer) := by
  have ambient {α : Type} (action : AmbientM α) :
      CompleteCarrier.Checked ledger debts locals (liftWGPrefix (monadLift action : WG.M α)) :=
    CompleteCarrier.native _ (fun initial => hoare_liftAmbient action (fun w=>StagedEntry.view w=initial))
  have conjunction (x y : Bool) : CompleteCarrier.Checked ledger debts locals
      (liftWGPrefix (WG.andM (branch .xmitEndpointNotInet x) (branch .xmitEndpointNotInet6 y))) := by
    apply CompleteCarrier.native
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a value v b run
    cases x <;> cases y
    all_goals simp [WG.andM,branch,AmbientM.branch] at run
    all_goals obtain ⟨⟨rfl,rfl⟩,rfl⟩:=run; rfl
  have binding {α β : Type} {action : WGPrefix Event α} {next : α → WGPrefix Event β}
      (head : CompleteCarrier.Checked ledger debts locals action)
      (tail : ∀ x, CompleteCarrier.Checked ledger debts locals (next x)) :
      CompleteCarrier.Checked ledger debts locals (action >>= next) := StatePrefixEnsures.bind head tail
  have pureChoice (value : Choice) : CompleteCarrier.Checked ledger debts locals (pure value) :=
    StatePrefixEnsures.pure _ (fun _ w _ before=>⟨w,before⟩) (fun _ _ _ before=>before)
  have walk (pid : PeerId) : CompleteCarrier.Checked ledger debts locals
      (do let packets ← liftWGPrefix (Packets.txWalk input.packets input.mtu [])
          let _ ← liftWGPrefix (branch .xmitWalk false)
          pure (Choice.splice pid packets)) := by
    apply binding (CompleteCarrier.native _ (OriginalRelease.store (RxCredits.txWalk_kernel _ _ _)))
    intro packets
    exact binding (ambient (AmbientM.branch .xmitWalk false)) (fun _=>pureChoice _)
  unfold choose chooseWith
  apply binding (ambient (AmbientM.branch .xmitNoPeer peer.isNone))
  intro missing
  split
  · apply binding (ambient (AmbientM.branch .xmitNoPeerInet (input.family == 4)))
    intro inet
    dsimp only
    split
    · exact binding (ambient (AmbientM.branch .xmitNoPeerInet6 (input.family == 6))) (fun _=>pureChoice _)
    · exact pureChoice _
  · cases peer with
    | none => exact pureChoice _
    | some pid =>
      apply binding (CompleteCarrier.native _ (Queued.read pid))
      intro resident
      apply binding (conjunction _ _)
      intro invalid
      split
      · exact pureChoice _
      · apply binding (ambient (AmbientM.branch .xmitValidDst true))
        intro ignored
        apply binding (ambient (AmbientM.branch .xmitNotGso (input.packets.length < 2)))
        intro small
        dsimp only
        split
        · apply binding (ambient (AmbientM.envOk .skbSegment))
          intro segment
          apply binding (ambient (AmbientM.branch .xmitGsoError (!segment)))
          intro failed
          split
          · exact pureChoice _
          · exact walk pid
        · exact walk pid

theorem choose_history (input : Input) (peer : Option PeerId) (w : WGWorld) (a : Ambient) (h : List Event) :
    (runWGPrefix (choose input peer) w a h).2=h := by
  have frame : StateHistoryFrame (fun e : Event=>some e) (choose input peer) := by
    unfold choose chooseWith
    repeat' first
      | (intro w a h; rfl)
      | apply StateHistoryFrame.bind
      | maintenance_intro
      | split
  change (runPrefix ((choose input peer).run w) a h).2=h
  simpa using frame w a h

theorem choose_account (input : Input) (peer : Option PeerId)
    (before : Accounted h ledger debts locals w)
    (run : runWGPrefix (choose input peer) w a h=(.ok ((value,v),b),last)) :
    last=h ∧ Accounted h ledger debts locals v := by
  have history := choose_history input peer w a h
  rw [run] at history
  obtain ⟨_,_,_,kept⟩:=choose_checked input peer w a h before
  change runPrefix ((choose input peer).run w) a h=_ at run
  rw [run] at kept
  exact ⟨history,history ▸ kept⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Transmit.Front
