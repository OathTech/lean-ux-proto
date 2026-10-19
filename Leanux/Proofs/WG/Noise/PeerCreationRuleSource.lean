import Leanux.Proofs.WG.Queues.BaseCreation

/-! Predicate-parametric contract for the existing actual allocation factor. Refusal and hidden-input Stops remain original. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Lifetimes Leanux.Proofs.Framing Std.Do Queues Queues.RxCredits

theorem peerCreate_rule (key : Key) (psk : Option Key)
    (P : WGWorld → Prop) (R : PeerId → WGWorld → Prop)
    (Q : Except Int PeerId → WGWorld → Prop)
    (read : Hoare getDev P (fun _=>P))
    (fail : ∀g,P g→Q (.error (-ENOMEM)) g)
    (core : ∀pid,Hoare (Peers.peerCreateCore pid key) P (fun _=>R pid))
    (finish : ∀pid,Hoare (BaseCreation.finish pid key psk) (R pid) (fun _=>Q (.ok pid))) :
    Hoare (peerCreate key psk) P Q := by
  have ambient {α : Type} (action : AmbientM α) :
      Hoare (StateT.lift action : WG.M α) P (fun _=>P) := hoare_liftAmbient action P
  have failed : Hoare (pure (.error (-ENOMEM)) : WG.M (Except Int PeerId)) P Q :=
    by
      apply (hoare_iff_run_ambient _ _ _).mpr
      intro g a result final b pre run
      cases run
      exact fail g pre
  rw [BaseCreation.peerCreate_factor]
  apply hoare_bind _ _ read
  intro d
  apply hoare_bind _ _ (ambient (AmbientM.branchCmp .peerCreateMaxPeers
    (d.numPeers ≥ MAX_PEERS_PER_DEVICE) d.numPeers MAX_PEERS_PER_DEVICE))
  intro maxed
  cases maxed with
  | true=>exact failed
  | false=>
    apply hoare_bind _ _ (ambient (AmbientM.hiddenAlloc .kmemCacheZallocPeer))
    intro allocated
    apply hoare_bind _ _ (ambient (AmbientM.branch .peerCreateNoMem (!allocated)))
    intro failedAlloc
    cases failedAlloc with
    | true=>exact failed
    | false=>
      apply hoare_bind _ _ (ambient (AmbientM.branch .peerCreateDstCacheFail false))
      intro cacheFailed
      cases cacheFailed with
      | true=>exact failed
      | false=>
        apply hoare_bind _ _ (core d.nextPeer)
        intro _
        apply hoare_bind _ _ (finish d.nextPeer)
        intro _
        apply (hoare_iff_run_ambient _ _ _).mpr
        intro g a result final b pre run
        cases run
        exact pre

end Leanux.Proofs.WG.Noise
