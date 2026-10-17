import Leanux.Proofs.WG.Index.OwnerCoherenceFrames
import Leanux.Proofs.WG.Config.EndpointSources

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do

/-- Owner-coherence variant of `Keypairs/Frames/WGBase.clearPeerEndpointSrc_spec`.
The owned exact source contract retains every peer word and reference count, including
all aliases; cache-clock errors remain stopped paths. -/
theorem clearPeerEndpointSrc_spec_ownerCoherent_variant (pid : PeerId) :
    Ensures (clearPeerEndpointSrc pid)
      (fun g => ∀d, g.dev = some d → HashedOwnersCoherent d)
      (fun _ g => ∀d, g.dev = some d → HashedOwnersCoherent d) := by
  intro g ambient result final after pre run
  cases device : g.dev with
  | none =>
    simp [clearPeerEndpointSrc,getPeer,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [clearPeerEndpointSrc,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      obtain ⟨next,reset,present,shape,selected,others⟩ :=
        Config.clearEndpointSource_exact pid d p resident g ambient result final after device run
      have table := congrArg Device.indexTable shape
      have keys := congrArg Device.keypairs shape
      intro actual actualPresent
      rw [present] at actualPresent
      cases actualPresent
      intro e member
      rw [table] at member
      obtain ⟨target,q,word,found,positive,owned⟩ := pre d device e member
      by_cases alias : target = pid
      · subst target
        have same : q = p := Option.some.inj (found.symm.trans resident)
        subst q
        refine ⟨pid,Config.clearedSource p reset,?_,selected,positive,?_⟩
        · cases kind : e.owner with
          | handshake own =>
            have self : pid = own := by simpa only [kind] using owned
            subst own
            simpa [kind,ownerWord,selected,Config.clearedSource,resident] using word
          | keypair key => simpa only [kind,ownerWord,keys] using word
        · cases kind : e.owner <;> simpa only [kind,keys] using owned
      · have selectedOther := (others target alias).trans found
        refine ⟨target,q,?_,selectedOther,positive,?_⟩
        · cases kind : e.owner with
          | handshake own =>
            have self : target = own := by simpa only [kind] using owned
            subst own
            simpa only [kind,ownerWord,selectedOther,found] using word
          | keypair key => simpa only [kind,ownerWord,keys] using word
        · cases kind : e.owner <;> simpa only [kind,keys] using owned


end Leanux.Proofs.WG.Index
