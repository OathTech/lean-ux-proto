import Leanux.Proofs.WG.Queues.HandshakeWorker
import Leanux.Proofs.WG.Queues.HolderDeviceCreate
import Leanux.Proofs.WG.Queues.BaseCoherence

/-! The original fixture supplies every local account entry fact. Physical
absence stays explicit; a fresh accounting cut is chosen at the actual journal,
without dropping old events or replacing an admission's selected ledger. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HolderInitial
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders

/-- Complete account fields depend on the subsystem store, so boot/prefill
changes elsewhere do not add an initialization premise. -/
theorem store (hi : Boundary cs loans w) (same : wgStoreView v=wgStoreView w) :
    Boundary cs loans v := by
  apply HolderEncrypt.boundary_fields hi
  have factor (w : WGWorld) :
      HolderEncrypt.fields {dev:=(wgStoreView w).dev,nlSock7 := (wgStoreView w).nlSock7, nlSock8 := (wgStoreView w).nlSock8}=HolderEncrypt.fields w := rfl
  rw [←factor v,←factor w,same]

theorem boundary (net bare : Bool) (w : WGWorld)
    (same : wgStoreView w=wgStoreView (Runner.initialWG net bare)) : Boundary [] [] w :=
  store (boundary_initial net bare) same

theorem coherent (net bare : Bool) (w : WGWorld)
    (same : wgStoreView w=wgStoreView (Runner.initialWG net bare)) : BaseCoherence.Inv w := by
  apply BaseCoherence.transport (BaseCoherence.initial net bare)
  exact congrArg (fun s : WGStoreView => BaseCoherence.view {dev:=s.dev}) same

/-- Both fixture flags, including absent-device cases, establish the complete
initial tuple over the actual product World and empty observation history. -/
theorem initial (net bare : Bool) (w : World)
    (same : wgStoreView w.wg=wgStoreView (Runner.initialWG net bare)) :
    Boundary [] [] w.wg ∧ HolderDeviceCreate.OptionalPhysical w.wg ∧
      OwnerChecks.Inv [] w ∧ CurrentSlots.Inv w.wg ∧ BaseCoherence.Inv w.wg :=
  ⟨boundary net bare w.wg same,HolderDeviceCreate.physical_initial net bare w.wg same,
    OwnerChecks.initial net bare w same,CurrentSlots.initial net bare w.wg same,
    coherent net bare w.wg same⟩

/-- A present device selects the real ring branch; no empty ring is fabricated
for the absent case. -/
theorem physical_present (physical : HolderDeviceCreate.OptionalPhysical w.wg)
    (present : w.wg.dev.isSome=true) : DecryptIteration.Physical w := by
  rcases physical with absent | physical
  · simp [absent] at present
  · exact physical

/-- Start the fixed-cut scheduler account at this exact incoming journal. -/
theorem at_cut (account : Boundary cs loans w.wg) (physical : DecryptIteration.Physical w)
    (owner : OwnerChecks.Inv h w) (slots : CurrentSlots.Inv w.wg) :
    HolderAuxiliary.Inv cs loans h h w :=
  ⟨⟨HolderNapi.at_start account h,physical⟩,owner,slots⟩

/-- Rebase only after extracting the original cut's actual removal suffix.
The new ledger is precisely the old ledger minus those removals. -/
theorem rebase (hi : HolderAuxiliary.Inv cs loans before h w) :
    ∃ suffix, h=before++suffix ∧
      HolderAuxiliary.Inv (remaining cs (NapiCarrier.removedPackets suffix)) loans h h w := by
  obtain ⟨suffix,history,account⟩ := hi.1.1
  exact ⟨suffix,history,at_cut account hi.1.2 hi.2.1 hi.2.2⟩

/-- A schedule starting at the actual present fixture needs no supplied
funding/owner invariant. This is a single schedule, not the initialized runner. -/
theorem initial_schedule (net bare : Bool) (w : World) (stack : Option Worker)
    (same : wgStoreView w.wg=wgStoreView (Runner.initialWG net bare))
    (present : w.wg.dev.isSome=true) :
    ∃ suffix, (runPrefix (RxHistory.schedule stack) w []).2=[]++suffix ∧
      OwnerChecks.Safe ([]++suffix) ∧
      (match (runPrefix (RxHistory.schedule stack) w []).1 with
       | .error _ => True
       | .ok (_,v) => HolderAuxiliary.Inv [] [] [] ([]++suffix) v) := by
  have entry := initial net bare w same
  obtain ⟨suffix,history,safe,post⟩ := HandshakeWorker.schedule [] [] [] stack w []
    (at_cut entry.1 (physical_present entry.2.1 present) entry.2.2.1 entry.2.2.2.1)
  refine ⟨suffix,history,history ▸ safe,?_⟩
  cases result : (runPrefix (RxHistory.schedule stack) w []).1 with
  | error e => trivial
  | ok pair =>
    rw [result] at post
    simpa only [←history] using post

end Leanux.Proofs.WG.Queues.RxCredits.HolderInitial
