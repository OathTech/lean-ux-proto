import Leanux.Proofs.WG.Index.CreationIndexEffects
import Leanux.Proofs.WG.Queues.BaseCreation
import Leanux.Proofs.WG.Lifetimes.PeerAllocation

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Leanux.Proofs.Framing Lifetimes
open Queues.RxCredits

/-- Normal original creation derives its selected vacant cursor from the
same entry's configured invariant. Errno returns retain the old device;
success uses existing exact footprint and allocation geometry, not a new
initialization traversal or a supplied output-state condition. -/
theorem peerCreate_hashSlots_retirement_source
    (publicKey : Key) (psk : Option Key) (retired : Reservations) :
    Ensures (peerCreate publicKey psk)
      (fun w => ConfiguredIdentity.Inv w ∧
        (∀ d, w.dev = some d → HashSlotCoverage d) ∧
        (∀ d, w.dev = some d → DeadHashedReserved retired d))
      (fun _ w => (∀ d, w.dev = some d → HashSlotCoverage d) ∧
        (∀ d, w.dev = some d → DeadHashedReserved retired d)) := by
  intro w a result v b pre run
  cases device : w.dev with
  | none =>
    simp [peerCreate,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    have effect := peerCreate_owner_fields publicKey psk d w a result v b device run
    cases result with
    | error code =>
      exact ⟨fun current out => by
          have same : current = d := Option.some.inj (out.symm.trans effect)
          subst current
          exact pre.2.1 d device,
        fun current out => by
          have same : current = d := Option.some.inj (out.symm.trans effect)
          subst current
          exact pre.2.2 d device⟩
    | ok pid =>
      obtain ⟨current,p,out,footprint,resident,unit,self,tag⟩ := effect
      have geometry := peerCreate_geometry publicKey psk w v (.ok pid) a b run
      have cursor : d.nextPeer = pid := by
        simpa only [device,Option.map_some,Option.some.injEq] using geometry.2.2
      have vacant : d.peers[pid]? = none := by
        rw [← cursor]
        exact BaseCreation.frontier_vacant pre.1 device
      obtain ⟨old,oldDevice,epoch,_,_,_⟩ := geometry.device out
      have sameOld : old = d := Option.some.inj (oldDevice.symm.trans device)
      subst old
      have slots := peerCreateFootprint_hashSlots d current pid footprint vacant (pre.2.1 d device)
      have reserved := peerCreateFootprint_retirement d current pid footprint vacant epoch
        (pre.2.1 d device) retired (pre.2.2 d device)
      constructor
      · intro final finalDevice
        have same : final = current := Option.some.inj (finalDevice.symm.trans out)
        exact same ▸ slots
      · intro final finalDevice
        have same : final = current := Option.some.inj (finalDevice.symm.trans out)
        exact same ▸ reserved
end Leanux.Proofs.WG.Index
