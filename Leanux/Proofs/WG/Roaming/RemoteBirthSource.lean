import Leanux.Proofs.WG.Roaming.RemoteBirthFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteBirth
open Leanux Leanux.WG Noise Lifetimes Queues Queues.RxCredits Leanux.Proofs.Framing Std.Do

theorem peerCreate_remotes (key : Key) (psk : Option Key) (entry : RemoteMap) :
    Ensures (peerCreate key psk) (fun g => destinationAt g = entry)
      (fun result g => destinationAt g = birthRemotes entry result) := by
  let P : WGWorld → Prop := fun g => destinationAt g = entry
  let Q := fun (result : Except Int PeerId) (g : WGWorld) =>
    destinationAt g = birthRemotes entry result
  have ambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient action P)
  have fail : Ensures (pure (.error (-ENOMEM)) : WG.M (Except Int PeerId)) P Q := by
    intro g a result final b pre run
    cases run
    exact pre
  have reader : Ensures getDev P (fun _ => P) := by
    intro g a result final b pre run
    cases device : g.dev <;> simp [getDev,device,invariant,AmbientM.invariant] at run
    · cases run
    · obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
      exact pre
  have core (pid : PeerId) :
      Ensures (Peers.peerCreateCore pid key) P
        (fun _ g => destinationAt g = birthRemotes entry (.ok pid)) := by
    intro g a result final b pre run
    rw [Peers.peerCreateCore_run] at run
    cases run
    rw [creationCore_remotes,pre]
  rw [BaseCreation.peerCreate_factor]
  refine ensures_bind _ _ reader ?_
  intro d
  refine ensures_bind _ _ (ambient (AmbientM.branchCmp .peerCreateMaxPeers
    (d.numPeers ≥ MAX_PEERS_PER_DEVICE) d.numPeers MAX_PEERS_PER_DEVICE)) ?_
  intro maxed
  cases maxed with
  | true => exact fail
  | false =>
    refine ensures_bind _ _ (ambient (AmbientM.hiddenAlloc .kmemCacheZallocPeer)) ?_
    intro allocated
    refine ensures_bind _ _ (ambient (AmbientM.branch .peerCreateNoMem (!allocated))) ?_
    intro failed
    cases failed with
    | true => exact fail
    | false =>
      refine ensures_bind _ _ (ambient (AmbientM.branch .peerCreateDstCacheFail false)) ?_
      intro cacheFailed
      cases cacheFailed with
      | true => exact fail
      | false =>
        refine ensures_bind _ _ (core d.nextPeer) ?_
        intro _
        refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
          (finish_remotes d.nextPeer key psk (birthRemotes entry (.ok d.nextPeer)))) ?_
        intro _ g a result final b pre run
        cases run
        exact pre

theorem receipt_effect (r : PeerCreateReceipt) (valid : DriverTags.PeerCreateValid r) :
    BirthRemoteEffect r := by
  refine ⟨valid.effect.1,?_⟩
  obtain ⟨g,a,final,b,beforeEq,afterEq,run⟩ := valid
  rw [afterEq,beforeEq]
  exact peerCreate_remotes r.publicKey r.presharedKey (destinationAt g)
    g a r.result final b rfl run

end Leanux.Proofs.WG.Roaming.RemoteBirth
