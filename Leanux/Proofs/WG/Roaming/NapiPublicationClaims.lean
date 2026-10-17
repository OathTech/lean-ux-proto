import Leanux.Proofs.WG.Roaming.NapiPublicationOwnerSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Env Noise

theorem observedNativeDecryptFirstPoll_authenticated :
    Campaign2.Product.Ensures observedNativeDecryptFirstPoll (fun _ => True)
      (fun result _ => NativePublicationOwnerObservation result) := by
  have pubPrefix : Noise.Product.Ensures (publicationPrefix napiSoftirq) (fun _ => True)
      (fun found w => ∀ pub, found = some pub →
        pub.publication = Campaign2.Product.snapshot w ∧ PublishedAuthentication pub ∧
        OwnerScheduled pub.publication pub.owner) := by
    intro w found final pre run pub same
    obtain ⟨snapshot,auth⟩ := publicationPrefix_authenticated napiSoftirq w found final pre run pub same
    exact ⟨snapshot,auth,publicationPrefix_scheduled napiSoftirq w found final pre run pub same⟩
  have constant {α : Type} (action : Leanux.M α) (P : Prop) :
      Noise.Product.Ensures action (fun _ => P) (fun _ _ => P) := by
    intro _ _ _ pre _; exact pre
  unfold observedNativeDecryptFirstPoll
  refine Noise.Product.ensures_bind _ _ pubPrefix ?_
  intro found
  cases found with
  | none =>
    intro w result final pre run
    cases run
    refine ⟨rfl,?_⟩
    intro pub first impossible
    cases impossible
  | some pub =>
    have irq : Noise.Product.Ensures observedNapiIrqFirst
        (fun w => ∀ p, some pub = some p →
          p.publication = Campaign2.Product.snapshot w ∧ PublishedAuthentication p ∧
          OwnerScheduled p.publication p.owner)
        (fun first _ => NativePublicationOwnerObservation (true,some (pub,first))) := by
      intro w first final pre run
      obtain ⟨snapshot,auth,owned⟩ := pre pub rfl
      have actual := observedNapiIrqFirst_facts pub.owner pub.publication w first final
        ⟨snapshot.symm,owned⟩ run
      refine ⟨rfl,?_⟩
      intro p other same
      cases same
      refine ⟨auth,owned,actual,?_⟩
      intro cut selected endpoint atEndpoint observed head
      obtain ⟨_,_,facts⟩ := actual cut selected
      obtain ⟨endpointFacts,queue⟩ := facts endpoint atEndpoint observed
      have identity : endpoint.id = pub.id := Option.some.inj (queue.symm.trans head)
      exact ⟨identity,publication_poll_authentication pub.owner pub endpoint auth endpointFacts identity⟩
    refine Noise.Product.ensures_bind _ _ irq ?_
    intro first
    refine Noise.Product.ensures_bind _ _ (constant (liftWG (peerPut (some pub.owner))) _) ?_
    intro ignored
    refine Noise.Product.ensures_bind _ _ (constant napiSoftirq _) ?_
    intro ignored w result final pre run
    cases run
    exact pre


end Leanux.Proofs.WG.Roaming
