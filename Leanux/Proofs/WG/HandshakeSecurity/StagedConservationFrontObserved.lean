import Leanux.Proofs.WG.HandshakeSecurity.StagedConservationFrontFrames
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeDecoration

/-! The existing transmit-front callback can record input obligations and
actual staged disposals while retaining its exact earlier routing receipt.
This is a local source observer; coverage of every caller remains separate. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Front
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Packets

structure Input where
  family : Nat
  address : Nat
  packets : List Packet
  mtu : Nat

def observedOps (record : StagedDisposal.Event → E)
    (decode : E → Option StagedDisposal.Event) : Ops (WGPrefix E) where
  step := liftWGPrefix
  put := fun peer => focusStatePrefix record decode (StagedDisposal.releaseObserved peer)
  trim := fun pid => focusStatePrefix record decode (StagedDisposal.overflowObserved pid)
  splice := fun pid packets => liftWGPrefix (xmitSplice pid packets)

theorem observedOps_erases (record : StagedDisposal.Event → E)
    (decode : E → Option StagedDisposal.Event) : Ops.Erases (observedOps record decode) where
  step := fun _ => erasesStatePrefix_lift _
  put := fun peer => focusStatePrefix_erases record decode (StagedDisposal.release_erases peer)
  trim := fun pid => focusStatePrefix_erases record decode (StagedDisposal.overflow_erases pid)
  splice := fun _ _ => erasesStatePrefix_lift _

theorem observedOps_frame (record : StagedDisposal.Event → E)
    (decode : E → Option StagedDisposal.Event) (ρ : E → Option F)
    (quiet : ∀ event, ρ (record event) = none) : Ops.HistoryFrame ρ (observedOps record decode) where
  step := fun _ _ _ _ => rfl
  put := fun peer w => focusPrefix_other record decode ρ quiet ((StagedDisposal.releaseObserved peer).run w)
  trim := fun pid w => focusPrefix_other record decode ρ quiet ((StagedDisposal.overflowObserved pid).run w)
  splice := fun _ _ _ _ _ => rfl

theorem observedOps_appends (record : StagedDisposal.Event → E)
    (decode : E → Option StagedDisposal.Event) : Ops.Appends (observedOps record decode) where
  step := fun _ => StateAppends.lift _
  put := fun peer => StateAppends.focus record decode (StagedDisposal.releaseObserved peer)
  trim := fun pid => StateAppends.focus record decode (StagedDisposal.overflowObserved pid)
  splice := fun _ _ => StateAppends.lift _

theorem observed_front_projects (record : StagedDisposal.Event → E)
    (decode : E → Option StagedDisposal.Event) (ρ : E → Option F)
    (quiet : ∀ event, ρ (record event) = none) (input : Input) :
    StateProjectsPrefix ρ id
      (frontWith (observedOps record decode) input.family input.address input.packets input.mtu)
      (liftWGPrefix (txFront input.family input.address input.packets input.mtu)) :=
  Exchange.quiet_native_projection ρ _ _
    (front_erases (observedOps_erases record decode) _ _ _ _)
    (front_frame (observedOps_frame record decode ρ quiet) _ _ _ _)

/-- Entry precedes every protocol/routing/error arm. The routed receipt wraps
this same run, while a counted erase remains recorded if a later arm stops. -/
def observed (entry : Input → E) (record : StagedDisposal.Event → E)
    (decode : E → Option StagedDisposal.Event)
    (routed : Input → WGRunWitness (Except Int PeerId) → E) (input : Input) :
    WGPrefix E (Except Int PeerId) := do
  emitStatePrefix (entry input)
  receiptWGObserved
    (frontWith (observedOps record decode) input.family input.address input.packets input.mtu)
    (routed input)

/-- Every execution retains its actual entry, even if the native front stops
before either a routing result or a terminal error receipt can be produced. -/
theorem observed_retains_entry (entry : Input → E) (record : StagedDisposal.Event → E)
    (decode : E → Option StagedDisposal.Event)
    (routed : Input → WGRunWitness (Except Int PeerId) → E) (input : Input)
    (w : WGWorld) (a : Ambient) (h : List E) :
    ∃ suffix, (runWGPrefix (observed entry record decode routed input) w a h).2 =
      h ++ entry input :: suffix := by
  have appends := StateAppends.receiptWGObserved
    (front_appends (observedOps_appends record decode) input.family input.address input.packets input.mtu)
    (routed input)
  obtain ⟨suffix,equation⟩ := appends w a (h ++ [entry input])
  refine ⟨suffix,?_⟩
  change (runStatePrefix (observed entry record decode routed input) w a h).2 = _
  rw [observed,runStatePrefix_bind,runStatePrefix_emit]
  simpa only [runStatePrefix,List.append_assoc,List.singleton_append] using equation

theorem observed_erases (entry : Input → E) (record : StagedDisposal.Event → E)
    (decode : E → Option StagedDisposal.Event)
    (routed : Input → WGRunWitness (Except Int PeerId) → E) (input : Input) :
    ErasesStatePrefix (observed entry record decode routed input)
      (txFront input.family input.address input.packets input.mtu) := by
  unfold observed
  have body := receiptWGObserved_erases
    (front_erases (observedOps_erases record decode) input.family input.address input.packets input.mtu)
    (routed input)
  simpa only [pure_bind] using
    (erasesStatePrefix_bind (erasesStatePrefix_emit (entry input)) (fun _ => body))

theorem observed_projects (entry : Input → E) (record : StagedDisposal.Event → E)
    (decode : E → Option StagedDisposal.Event)
    (routed : Input → WGRunWitness (Except Int PeerId) → E)
    (target : Input → WGRunWitness (Except Int PeerId) → F) (ρ : E → Option F)
    (entryQuiet : ∀ input, ρ (entry input) = none)
    (disposalQuiet : ∀ event, ρ (record event) = none)
    (routedMatch : ∀ input r, ρ (routed input r) = some (target input r)) (input : Input) :
    StateProjectsPrefix ρ id (observed entry record decode routed input)
      (receiptWGObserved
        (liftWGPrefix (txFront input.family input.address input.packets input.mtu)) (target input)) := by
  have entryProjection : StateProjectsPrefix ρ id
      (emitStatePrefix (entry input) : WGPrefix E Unit) (pure ()) := by
    intro w a h
    change (Except.ok (((),w),a),h.filterMap ρ) =
      (Except.ok (((),w),a),(h ++ [entry input]).filterMap ρ)
    simp only [List.filterMap_append,List.filterMap_cons,entryQuiet,List.filterMap_nil,List.append_nil]
  have body := Exchange.receipt_projects ρ _ _ (routed input) (target input)
    (observed_front_projects record decode ρ disposalQuiet input) (routedMatch input)
  simpa only [observed,pure_bind] using
    (StateProjectsPrefix.bind
      (f := fun (_ : Unit) => receiptWGObserved
        (frontWith (observedOps record decode) input.family input.address input.packets input.mtu) (routed input))
      (b := fun (_ : Unit) => receiptWGObserved
        (liftWGPrefix (txFront input.family input.address input.packets input.mtu)) (target input))
      ρ id id entryProjection (fun _ => body))

end Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Front
