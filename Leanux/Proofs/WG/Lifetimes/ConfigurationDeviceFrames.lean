import Leanux.Proofs.WG.Lifetimes.ConfigurationPeer
import Leanux.Proofs.Framing.WGConfiguration

/-! The device-only configuration frame and the existing peer precomputation
observer focused into mixed history. Precomputation's saved write and later
fresh getter stay in the checked peer observer; only state transport is added. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

theorem configuration_identity_metadata (w v : World)
    (he : configurationView v = configurationView w) :
    (identityView v, allocationMetadata v) = (identityView w, allocationMetadata w) := by
  have hi := congrArg (fun k => identityView {w with k}) he
  have hm := congrArg (fun k => allocationMetadata {w with k}) he
  apply Prod.ext
  · unfold identityView Peers.snapshot keypairResidents packetResidents at hi ⊢
    simpa [configurationView, configurationKernel, configurationDevice, Option.bind_map, Function.comp_def] using hi
  · unfold allocationMetadata deviceAllocationMetadata at hm ⊢
    simpa [configurationView, configurationKernel, configurationDevice, Option.map_map, Function.comp_def] using hm

def ConfigurationStable (I : List LifetimeEvent → World → Prop) : Prop :=
  ∀ h w v, configurationView v = configurationView w → I h w → I h v

theorem allocationConfigurationStable : ConfigurationStable AllocationInv := by
  intro h w v he hi
  have hf := configuration_identity_metadata w v he
  exact hi.congr (congrArg Prod.fst hf) (congrArg Prod.snd hf)

theorem configurationLift_preserves (c : AmbientContracts I) (hc : ConfigurationStable I)
    (a : M α) (ha : SameConfiguration a) :
    PrefixPreserves I LifetimeEvent.Safe (liftPrefix a) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift a c.safe
  intro h w x v hi hr
  exact hc h w v (ha w x v hr) hi

theorem generation_sameConfiguration : SameConfiguration
    (modifyDev fun d => {d with deviceUpdateGen := d.deviceUpdateGen + 1}) := by
  apply SameView.of_wp
  intro s
  exact modifyDev_configuration_spec (fun t => t = s) _ (fun _ => rfl)

theorem fwmark_sameConfiguration (mark : Nat) : SameConfiguration
    (modifyDev fun d => {d with fwmark := mark}) := by
  apply SameView.of_wp
  intro s
  exact modifyDev_configuration_spec (fun t => t = s) _ (fun _ => rfl)

def precomputeStaticStaticMixed (pid : PeerId) : MixedM Unit :=
  peerFocus (Peers.precomputeStaticStaticPrefix pid)

theorem precomputeStaticStaticMixed_erases (pid : PeerId) :
    ErasesPrefix (precomputeStaticStaticMixed pid) (precomputeStaticStatic pid) :=
  peerFocus_erases (Peers.precomputeStaticStaticPrefix_erases pid)

theorem precomputeStaticStaticMixed_allocation (pid : PeerId) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (precomputeStaticStaticMixed pid) := by
  intro w h hi
  obtain ⟨suffix, hsuf, hsafe, hout⟩ := Peers.precomputeStaticStaticPrefix_spec (fun _ => True) pid w
    (h.filterMap LifetimeEvent.peer?) ⟨hi.peer, trivial⟩
  have hr : runPrefix (Peers.precomputeStaticStaticPrefix pid) w (h.filterMap LifetimeEvent.peer?) =
      ((runPrefix (Peers.precomputeStaticStaticPrefix pid) w (h.filterMap LifetimeEvent.peer?)).1,
        h.filterMap LifetimeEvent.peer? ++ suffix) := Prod.ext rfl hsuf
  unfold precomputeStaticStaticMixed peerFocus
  rw [focusPrefix_suffix _ _ _ _ _ _ _ hr]
  have hp : (h ++ suffix.map LifetimeEvent.peer).filterMap LifetimeEvent.peer? =
      h.filterMap LifetimeEvent.peer? ++ suffix := by
    rw [List.filterMap_append, filterMap_encoded LifetimeEvent.peer LifetimeEvent.peer? (fun _ => rfl)]
  have hk : (h ++ suffix.map LifetimeEvent.peer).filterMap LifetimeEvent.keypair? =
      h.filterMap LifetimeEvent.keypair? := by
    rw [List.filterMap_append, filterMap_disjoint _ _ (fun _ => rfl), List.append_nil]
  have ht : (h ++ suffix.map LifetimeEvent.peer).filterMap LifetimeEvent.packet? =
      h.filterMap LifetimeEvent.packet? := by
    rw [List.filterMap_append, filterMap_disjoint _ _ (fun _ => rfl), List.append_nil]
  refine ⟨suffix.map LifetimeEvent.peer, rfl, ?_, ?_⟩
  · exact ⟨by simpa only [hp, hsuf] using hsafe,
      hk ▸ hi.release.1.keypair.1, ht ▸ hi.release.1.packet.1⟩
  · cases ho : (runPrefix (Peers.precomputeStaticStaticPrefix pid) w (h.filterMap LifetimeEvent.peer?)).1 with
    | error e => trivial
    | ok out =>
      have original := (Peers.precomputeStaticStaticPrefix_erases pid w _).symm.trans ho
      have hg := precomputeStaticStatic_peerInitView pid w out.1 out.2 original
      have hs := Peers.precomputeStaticStatic_samePeerSnapshot pid w out.1 out.2 original
      have he : identityView out.2 = identityView w := Prod.ext hs (congrArg Prod.fst hg)
      have hm : allocationMetadata out.2 = allocationMetadata w := congrArg Prod.snd hg
      exact hi.peerTransport (result := .error 0) ⟨congrArg Prod.fst hg, hm, trivial⟩
        (by simpa only [hp, hsuf, ho, and_true] using hout)
        (hi.congr he hm).peerSlots hk ht

end Leanux.Proofs.WG.Lifetimes
