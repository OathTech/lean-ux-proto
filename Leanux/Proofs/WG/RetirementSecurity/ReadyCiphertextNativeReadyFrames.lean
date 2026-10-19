import Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertextNativeHandshakeFrames

/-! Immediate saved-peer updates retain the batch projection only when their
actual queue fields are preserved. Arbitrary stale setters are not frames. -/
namespace Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertext.Native
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity Queues.RxCredits

theorem peer_update (pid : PeerId) (f : Peer → Peer)
    (stamp : ∀ p, (f p).internalId = p.internalId)
    (queue : ∀ p, (f p).txQueue.all = p.txQueue.all) :
    Preserves (Coherent locals active) (getPeer pid >>= fun p => setPeer pid (f p)) := by
  apply coherent_join (OccurrenceHandshake.peer_update pid f stamp queue)
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,u,c,readRun,writeRun⟩ := run
  obtain ⟨same,clock,d,device,stored⟩ := Origins.getPeer_return pid w u p a c readRun
  subst u
  subst c
  cases writeRun
  simpa only [replacePeer,device,Option.map_some] using replace_peer before device stored (queue p)

theorem peer_update_bind (pid : PeerId) (f : Peer → Peer) (tail : Unit → WG.M α)
    (stamp : ∀ p, (f p).internalId = p.internalId)
    (queue : ∀ p, (f p).txQueue.all = p.txQueue.all)
    (next : ∀ x, Preserves (Coherent locals active) (tail x)) :
    Preserves (Coherent locals active) (getPeer pid >>= fun p => setPeer pid (f p) >>= tail) := by
  simpa only [bind_assoc] using preserves_bind (peer_update pid f stamp queue) next

theorem coherent_modify_device (f : Device → Device)
    (identities : ∀w,identityView {w with dev:=w.dev.map f}=identityView w)
    (metadata : ∀w,allocationMetadata {w with dev:=w.dev.map f}=allocationMetadata w)
    (wire : ∀w,txCryptWire {w with dev:=w.dev.map f}=txCryptWire w)
    (queues : ∀w,handoffTxView {w with dev:=w.dev.map f}=handoffTxView w) :
    Preserves (Coherent locals active) (modifyDev f) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have physical := (hoare_iff_run_ambient _ _ _).mp
    (OccurrenceHandshake.modify_device f identities metadata wire queues)
    w a result v b before.1 run
  refine ⟨physical,?_⟩
  cases run
  apply before.2.frame
  dsimp only [view]
  apply Prod.ext (queues w)
  funext id
  exact congrFun (congrArg Prod.snd (wire w)) id

macro "ready_ciphertext_coherent_step" : tactic => `(tactic| first
  | (receive_update_head setPeer; apply peer_update <;> intro p <;> rfl)
  | (receive_update_head Bind.bind
     apply peer_update_bind
     · intro p; rfl
     · intro p; rfl
     intro x)
  | (rx_retention_head getPeer; exact getPeer_preserves _ _)
  | (rx_retention_head getDev; exact coherent_store getDev_sameWGStore)
  | (rx_retention_head modifyDev
     apply coherent_modify_device
     · intro w; unfold identityView Peers.snapshot keypairResidents packetResidents; simp [Option.bind_map,Function.comp_def]
     · intro w; simp [allocationMetadata,deviceAllocationMetadata,Option.map_map,Function.comp_def] <;> rfl
     · intro w; simp [txCryptWire,TxRing.nativeCell,TxDisposition.txPackets,Option.map_map,Option.bind_map,Function.comp_def]
     · intro w; funext pid; simp [handoffTxView,Option.bind_map,Function.comp_def])
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (rx_retention_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) _)
  | rxstack_preserves_join
  | rx_retention_step)


end Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertext.Native
