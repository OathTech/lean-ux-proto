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

def freshDeviceWorld (w : World) : World :=
  {w with k := {w.k with netIfindexNext := w.k.netIfindexNext + 1, wg := some {ifindex := w.k.netIfindexNext, ifname := "wg0"}}}

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

def linkWorld (w : World) (v : WGKernelView) : World :=
  {w with k := {w.k with wg := v.wg, peerCounter := v.peerCounter, keypairCounter := v.keypairCounter, netIfindexNext := v.netIfindexNext}}

theorem linkView_identity_metadata (w v : World) (he : linkView v = linkView w) :
    (identityView v, allocationMetadata v) = (identityView w, allocationMetadata w) := by
  have hi := congrArg (fun s => identityView (linkWorld w s)) he
  have hm := congrArg (fun s => allocationMetadata (linkWorld w s)) he
  apply Prod.ext
  · unfold identityView Peers.snapshot keypairResidents packetResidents at hi ⊢
    simpa [linkWorld, linkView, linkKernel, linkDevice, WGKernelView.ofKernel,
      Option.bind_map, Function.comp_def] using hi
  · unfold allocationMetadata deviceAllocationMetadata at hm ⊢
    simpa [linkWorld, linkView, linkKernel, linkDevice, WGKernelView.ofKernel,
      Option.map_map, Function.comp_def] using hm

theorem freshDevice_linkView (w : World) :
    linkView (freshDeviceWorld w) = registeredLink (setupLink (linkView w)) := rfl

theorem wgCreate_allocation_endpoint (hi : AllocationInv h w)
    (hr : wgCreate.run w = .ok (ret,v)) : AllocationInv h v := by
  have he := (hoare_iff_triple _ _ _).mpr (wgCreate_endpoint (linkView w)) w ret v rfl hr
  rcases he with same | ⟨_,fresh⟩
  · have hf := linkView_identity_metadata w v same
    exact hi.congr (congrArg Prod.fst hf) (congrArg Prod.snd hf)
  · have hf := linkView_identity_metadata (freshDeviceWorld w) v
      (fresh.trans (freshDevice_linkView w).symm)
    exact hi.freshDevice.congr (congrArg Prod.fst hf) (congrArg Prod.snd hf)

def wgCreatePrefix : MixedM Int := liftPrefix wgCreate

theorem wgCreatePrefix_erases : ErasesPrefix wgCreatePrefix wgCreate := erasesPrefix_lift _

theorem wgCreatePrefix_allocation :
    PrefixPreserves AllocationInv LifetimeEvent.Safe wgCreatePrefix := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift wgCreate (fun _ _ hi => hi.safe)
  intro h w x v hi hr
  exact wgCreate_allocation_endpoint hi hr

end Leanux.Proofs.WG.Lifetimes
