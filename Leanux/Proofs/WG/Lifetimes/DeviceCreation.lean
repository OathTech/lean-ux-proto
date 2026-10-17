import Leanux.Proofs.WG.Lifetimes.DeviceRetirement
import Leanux.Proofs.Framing.WGDeviceLifecycle

/-! Creation is observed at the complete guarded original action. Its temporary
ifindex 0 is not an allocation epoch and need not satisfy AllocationInv. Source
inspection shows setup/newlink access no resident peer, keypair or packet. The
successful creation endpoint registers an empty device at the old fresh epoch;
existing-device and allocation-refusal returns keep their original alternatives.
Stops preserve the incoming access history. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def freshDeviceWorld (w : WGWorld) : WGWorld :=
  {w with netIfindexNext := w.netIfindexNext + 1, dev := some {ifindex := w.netIfindexNext, ifname := "wg0"}}

theorem AllocationInv.freshDevice (hi : AllocationInv h w) :
    AllocationInv h (freshDeviceWorld w) := by
  have hpkt : packetResidents (freshDeviceWorld w) = fun _ => none := by
    funext i; cases i <;> rfl
  have hr : ReleaseInv h (freshDeviceWorld w) := by
    refine ⟨⟨⟨hi.safe.1, ?_, ?_⟩, ⟨hi.safe.2.1, ?_⟩, ⟨hi.safe.2.2, ?_⟩⟩, ?_, ?_⟩
    all_goals try (simp only [identityView]; rw [hpkt]; simp [ResidentUnique])
    all_goals simp [freshDeviceWorld, Peers.snapshot, keypairResidents,
      identityView, Unique, Absent, ResidentUnique]
    intro a b hs i
    cases i <;> simp [packetResidents]
  refine ⟨hr, ⟨hr.1.peer, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Bounded, Peers.snapshot, freshDeviceWorld]
  · exact hi.peer.pastBounded
  · simp [freshDeviceWorld]
  · simp [Bounded, keyStore, keypairResidents, freshDeviceWorld]
  · exact hi.keyPast
  · simp [freshDeviceWorld]
  · intro d hd
    simp only [freshDeviceWorld, Option.some.injEq] at hd
    subst d
    intro i stamp hl
    cases i <;> simp [Packets.deviceStore] at hl
  · simp [freshDeviceWorld]
  · intro stamp hs
    exact Nat.lt_trans (hi.packetPastEpoch stamp hs) (Nat.lt_succ_self _)
  · intro d hd stamp hs
    simp only [freshDeviceWorld, Option.some.injEq] at hd
    subst d
    exact False.elim (Nat.lt_irrefl _ (hi.packetPastEpoch _ hs))

theorem linkView_identity_metadata (w v : WGWorld) (he : linkView v = linkView w) :
    (identityView v, allocationMetadata v) = (identityView w, allocationMetadata w) := by
  let observe : WGStoreView → IdentityView := fun s =>
    (⟨s.peerCounter, fun i => (s.dev.bind fun d => d.peers[i]?).map (·.internalId)⟩,
      (fun i => (s.dev.bind fun d => d.keypairs[i]?).map (·.internalId)),
      fun slot => s.dev.bind fun d => match slot with
        | .inl i => d.txSkbs[i]?.map (fun _ => (d.ifindex, i + 1))
        | .inr i => d.rxSkbs[i]?.map (fun _ => (d.ifindex, i + 1)))
  have hi := congrArg observe he
  have hm := congrArg (fun s : WGStoreView =>
    (⟨s.keypairCounter, s.netIfindexNext,
      s.dev.map deviceAllocationMetadata⟩ : AllocationMetadata)) he
  apply Prod.ext
  · apply Prod.ext
    · simpa [observe, identityView, Peers.snapshot, linkView, linkStore, linkDevice,
        wgStoreView, Option.bind_map, Function.comp_def] using congrArg Prod.fst hi
    · apply Prod.ext
      · change keypairResidents v = keypairResidents w
        unfold keypairResidents
        simpa [observe, linkView, linkStore, linkDevice,
          wgStoreView, Option.bind_map, Function.comp_def] using
          congrArg (fun s : IdentityView => s.2.1) hi
      · funext slot
        have ht := congrArg (fun s : IdentityView => s.2.2 slot) hi
        cases slot <;>
          simpa [observe, identityView, packetResidents, linkView, linkStore, linkDevice,
            wgStoreView, Option.bind_map, Function.comp_def] using ht
  · unfold allocationMetadata deviceAllocationMetadata
    simpa [deviceAllocationMetadata, linkView, linkStore, linkDevice, wgStoreView,
      Option.map_map, Function.comp_def] using hm

theorem freshDevice_linkView (w : WGWorld) :
    linkView (freshDeviceWorld w) = registeredLink (setupLink (linkView w)) := rfl

theorem wgCreate_allocation_endpoint (hi : AllocationInv h w)
    (hr : (wgCreate.run w).run ambient = .ok ((ret, v), ambient')) : AllocationInv h v := by
  have he := (hoare_iff_run_ambient _ _ _).mp (wgCreate_endpoint (linkView w))
    w ambient ret v ambient' rfl hr
  rcases he with same | ⟨_,fresh⟩
  · have hf := linkView_identity_metadata w v same
    exact hi.congr (congrArg Prod.fst hf) (congrArg Prod.snd hf)
  · have hf := linkView_identity_metadata (freshDeviceWorld w) v
      (fresh.trans (freshDevice_linkView w).symm)
    exact hi.freshDevice.congr (congrArg Prod.fst hf) (congrArg Prod.snd hf)

def wgCreatePrefix : MixedM Int := liftWGPrefix wgCreate

theorem wgCreatePrefix_erases : ErasesStatePrefix wgCreatePrefix wgCreate :=
  erasesStatePrefix_lift _

theorem wgCreatePrefix_allocation :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe wgCreatePrefix := by
  apply StatePrefixEnsures.lift wgCreate (fun _ _ _ hi => hi.safe)
  intro h w ambient x v ambient' hi hr
  exact wgCreate_allocation_endpoint hi hr

end Leanux.Proofs.WG.Lifetimes
