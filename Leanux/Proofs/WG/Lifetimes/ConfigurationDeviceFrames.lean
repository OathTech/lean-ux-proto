import Leanux.Proofs.WG.Lifetimes.ConfigurationPeer
import Leanux.Proofs.Framing.WGConfiguration

/-! The device-only configuration frame and the existing peer precomputation
observer focused into mixed history. Precomputation's saved write and later
fresh getter stay in the checked peer observer; only state transport is added. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def configurationStoreView (g : WGWorld) : WGStoreView :=
  (configurationView g).toWGStoreView

def productConfigurationView (w : World) : ProductStore43 :=
  (fsStoreView w.fs, w.tasks, (w.seccomp.filters, w.seccomp.nextFilter), configurationStoreView w.wg)

theorem configuration_identity_metadata (w v : WGWorld) (he : configurationStoreView v = configurationStoreView w) :
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
    · simpa [observe, identityView, Peers.snapshot, configurationStoreView, configurationView, configurationDevice, wgOwnedView,
        wgStoreView, Option.bind_map, Function.comp_def] using congrArg Prod.fst hi
    · apply Prod.ext
      · change keypairResidents v = keypairResidents w
        unfold keypairResidents
        simpa [observe, configurationStoreView, configurationView, configurationDevice, wgOwnedView,
          wgStoreView, Option.bind_map, Function.comp_def] using
          congrArg (fun s : IdentityView => s.2.1) hi
      · funext slot
        have ht := congrArg (fun s : IdentityView => s.2.2 slot) hi
        cases slot <;>
          simpa [observe, identityView, packetResidents, configurationStoreView, configurationView, configurationDevice, wgOwnedView,
            wgStoreView, Option.bind_map, Function.comp_def] using ht
  · unfold allocationMetadata deviceAllocationMetadata
    simpa [deviceAllocationMetadata, configurationStoreView, configurationView, configurationDevice, wgOwnedView, wgStoreView,
      Option.map_map, Function.comp_def] using hm

def ConfigurationStable (I : List LifetimeEvent → WGWorld → Prop) : Prop :=
  ∀ h w v, configurationStoreView v = configurationStoreView w → I h w → I h v

def ProductConfigurationStable (I : List LifetimeEvent → World → Prop) : Prop :=
  ∀ h w v, productConfigurationView v = productConfigurationView w → I h w → I h v

theorem allocationConfigurationStable : ConfigurationStable AllocationInv := by
  intro h w v he hi
  have hf := configuration_identity_metadata w v he
  exact hi.congr (congrArg Prod.fst hf) (congrArg Prod.snd hf)

theorem configurationLift_preserves (c : ProductAmbientContracts I) (hc : ProductConfigurationStable I)
    (a : Leanux.M α) (ha : SameView productConfigurationView a) :
    PrefixPreserves I LifetimeEvent.Safe (liftPrefix a) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift a c.safe
  intro h w x v hi hr
  exact hc h w v ((ProjectedAction.iff_run _ _ _).mp ha w x v hr) hi

theorem configurationLift_preserves_native (c : AmbientContracts I) (hc : ConfigurationStable I)
    (a : WG.M α) (ha : SameView configurationStoreView a) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix a) := by
  apply StatePrefixEnsures.lift a (fun h w _ hi => c.safe h w hi)
  intro h w ambient x v ambient' hi hr
  exact hc h w v ((ProjectedAction.iff_run_ambient _ _ _).mp ha w ambient x v ambient' hr) hi

theorem configurationLift_native_product (c : ProductAmbientContracts I) (hc : ProductConfigurationStable I)
    (a : WG.M α) (ha : SameView configurationStoreView a) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix a)) := by
  rw [liftWGObserver_lift]
  apply configurationLift_preserves c hc (liftWG a)
  apply sameView_liftWG productConfigurationView configurationStoreView a ha
  intro w g ambient hg
  change (_, _, _, configurationStoreView g) = (_, _, _, configurationStoreView w.wg)
  rw [hg]

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
  peerStateFocus (Peers.precomputeStaticStaticPrefix pid)

theorem precomputeStaticStaticMixed_erases (pid : PeerId) :
    ErasesStatePrefix (precomputeStaticStaticMixed pid) (precomputeStaticStatic pid) :=
  focusStatePrefix_erases _ _ (Peers.precomputeStaticStaticPrefix_erases pid)

theorem precomputeStaticStaticMixed_allocation (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe (precomputeStaticStaticMixed pid) := by
  intro w ambient h hi
  obtain ⟨suffix, hsuf, hsafe, hout⟩ := Peers.precomputeStaticStaticPrefix_spec (fun _ => True) pid w ambient
    (h.filterMap LifetimeEvent.peer?) ⟨hi.peer, trivial⟩
  have hr : runPrefix ((Peers.precomputeStaticStaticPrefix pid).run w) ambient (h.filterMap LifetimeEvent.peer?) =
      ((runPrefix ((Peers.precomputeStaticStaticPrefix pid).run w) ambient (h.filterMap LifetimeEvent.peer?)).1,
        h.filterMap LifetimeEvent.peer? ++ suffix) := Prod.ext rfl hsuf
  unfold precomputeStaticStaticMixed peerStateFocus focusStatePrefix
  dsimp only [StateT.run] at hsuf hsafe hout hr ⊢
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
  · cases ho : (runPrefix (Peers.precomputeStaticStaticPrefix pid w) ambient (h.filterMap LifetimeEvent.peer?)).1 with
    | error e => trivial
    | ok out =>
      rcases out with ⟨⟨result, v⟩, ambientNext⟩
      have original := (Peers.precomputeStaticStaticPrefix_erases pid w ambient _).symm.trans ho
      have hg := (ProjectedAction.iff_run_ambient _ _ _).mp (precomputeStaticStatic_peerInitView pid) w ambient result v ambientNext original
      have hs := (ProjectedAction.iff_run_ambient _ _ _).mp (Peers.precomputeStaticStatic_samePeerSnapshot pid) w ambient result v ambientNext original
      have he : identityView v = identityView w := Prod.ext hs (congrArg Prod.fst hg)
      have hm : allocationMetadata v = allocationMetadata w := congrArg Prod.snd hg
      exact hi.peerTransport (result := .error 0) ⟨congrArg Prod.fst hg, hm, trivial⟩
        (by simpa only [hp, hsuf, ho, and_true] using hout)
        (hi.congr he hm).peerSlots hk ht

end Leanux.Proofs.WG.Lifetimes
