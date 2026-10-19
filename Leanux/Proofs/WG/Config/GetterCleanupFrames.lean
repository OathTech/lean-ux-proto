import Leanux.Proofs.WG.Config.GetterMetadataFrames
import Leanux.Proofs.WG.Config.GetterCleanupMacFrames
import Leanux.Proofs.WG.Config.ReplacementCompletionSource
import Leanux.Proofs.WG.Index.CreatorSource
import Leanux.Proofs.WG.Index.SenderIndexSource
import Leanux.Proofs.WG.Index.BulkRemovalSource
import Leanux.Proofs.WG.Roaming.RemoteTimerFrames
import Leanux.Proofs.WG.Config.AllowedRemovalReadbackFrames
import Leanux.Proofs.WG.Index.AllowedFrameSource
import Leanux.Proofs.WG.Config.GetterCleanupAllowedSource
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.GetterCleanup
open Leanux Leanux.WG Noise TimerDiscipline Lifetimes Leanux.Proofs.Framing Std.Do

theorem ambient {α : Type} (action : AmbientM α) :
    SameView getterMetadata (StateT.lift action : WG.M α) :=
  fun _ => hoare_liftAmbient action _
theorem read_device : SameView getterMetadata getDev := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a x v b run
  cases hd : g.dev with
  | none => simp [getDev,hd,invariant,AmbientM.invariant] at run; cases run
  | some d =>
    simp [getDev,hd] at run
    rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
    rfl
theorem read_peer (pid : PeerId) : SameView getterMetadata (getPeer pid) := by
  intro initial
  exact hoare_consequence (getPeer_spec pid (fun g=>getterMetadata g=initial))
    (fun _ h=>h) (fun _ _ h=>h.1)
theorem modify_device (f : Device → Device)
    (same : ∀ d,sendConfiguration (f d)=sendConfiguration d) :
    SameView getterMetadata (modifyDev f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a x v b run
  cases run
  simp only [getterMetadata,Option.map_map,Function.comp_def,same]
theorem set_peer (pid : PeerId) (p : Peer) :
    SameView getterMetadata (setPeer pid p) :=
  modify_device _ (fun _=>rfl)
theorem modify_peer (pid : PeerId) (f : Peer → Peer) :
    SameView getterMetadata (modifyPeer pid f) :=
  read_peer pid |>.bind (fun p=>set_peer pid (f p))
theorem aip {α : Type} (action : AipM α) :
    SameView getterMetadata (liftAip action) := by
  intro initial
  apply hoare_liftAip
  intro g d store pre hd
  simpa only [getterMetadata,hd,Option.map_some,sendConfiguration] using pre
theorem index {α : Type} (action : IndexM α) :
    SameView getterMetadata (liftIndex action) := by
  intro initial
  apply hoare_liftIndex
  intro g d table pre hd
  simpa only [getterMetadata,hd,Option.map_some,sendConfiguration] using pre
theorem list_delete (id : NodeId) : SameView getterMetadata (listDel id) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a x v b run
  cases hd : g.dev with
  | none =>
    simp [listDel,getDev,hd,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    obtain ⟨r,out,c,actual,effect⟩ :=
      (total_iff_run_ambient _ _ _).mp (AllowedIps.listDel_wp g d hd id) g a rfl
    rw [run] at actual
    cases actual
    rw [effect.2]
    simp only [getterMetadata,hd,Option.map_some]
    rfl

theorem read_key (kid : KeypairId) : SameView getterMetadata (getKeypair kid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a x v b run
  cases hd : g.dev with
  | none => simp [getKeypair,getDev,hd,invariant,AmbientM.invariant] at run; cases run
  | some d =>
    cases hk : d.keypairs[kid]?
    · simp [getKeypair,getDev,hd,hk,invariant,AmbientM.invariant] at run; cases run
    · simp [getKeypair,getDev,hd,hk] at run
      rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
      rfl
theorem set_key (kid : KeypairId) (k : Keypair) :
    SameView getterMetadata (setKeypair kid k) :=
  modify_device _ (fun _=>rfl)
theorem dereference (owner : IndexOwner) :
    SameView getterMetadata (IndexOwner.peerDeref owner) :=
  fun _=>indexOwner_peerDeref_preserves owner _
/-- Narrow local variant of AllowedIps.rootRemove_clearListView for the
getter header/socket/fixture observation omitted by the seven-field store view. -/
theorem rootRemove_clearListView_getter_variant (root : NodeId) :
    SameView getterMetadata (rootRemovePeerLists root) :=
  fun initial=>rootRemove_preserves_source (fun g=>getterMetadata g=initial)
    (fun id=>(aip (getNode id)).wp (fun s=>s=initial))
    (fun id=>(list_delete id).wp (fun s=>s=initial)) root
theorem free_allowed : SameView getterMetadata WG.free := by
  intro initial
  change Preserves (fun g=>getterMetadata g=initial) _
  unfold WG.free
  repeat' first
    | (rx_retention_head getDev; exact read_device.wp (fun s=>s=initial))
    | (rx_retention_head modifyDev; apply (modify_device _ ?_).wp (fun s=>s=initial); intro d; rfl)
    | (rx_retention_head rootRemovePeerLists; exact (rootRemove_clearListView_getter_variant _).wp (fun s=>s=initial))
    | (allocation_release_lift_from AipM; exact (aip _).wp (fun s=>s=initial))
    | (rx_retention_head branch; exact hoare_liftAmbient (AmbientM.branch _ _) _)
    | (rx_retention_head ForIn.forIn
       apply Framing.list_view_spec id (fun g=>getterMetadata g=initial)
       intro x s
       change Preserves (fun g=>getterMetadata g=initial) _)
    | rx_retention_step


macro "getter_cleanup_step " initial:term : tactic => `(tactic| first
  | (rx_retention_head getDev; exact read_device.wp (fun s=>s=$initial))
  | (rx_retention_head getPeer; exact (read_peer _).wp (fun s=>s=$initial))
  | (rx_retention_head getKeypair; exact (read_key _).wp (fun s=>s=$initial))
  | (rx_retention_head setPeer; exact (set_peer _ _).wp (fun s=>s=$initial))
  | (rx_retention_head setKeypair; exact (set_key _ _).wp (fun s=>s=$initial))
  | (rx_retention_head modifyPeer; exact (modify_peer _ _).wp (fun s=>s=$initial))
  | (rx_retention_head modifyDev; apply (modify_device _ ?_).wp (fun s=>s=$initial); intro d; rfl)
  | (rx_retention_head IndexOwner.peerDeref; exact (dereference _).wp (fun s=>s=$initial))
  | (allocation_release_lift_from IndexM; exact (index _).wp (fun s=>s=$initial))
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (rx_retention_head branch; exact hoare_liftAmbient (AmbientM.branch _ _) _)
  | (rx_retention_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) _)
  | (rx_retention_head requireNotPending; unfold requireNotPending)
  | (rx_retention_head refcountDecAndTest; unfold refcountDecAndTest)
  | (rx_retention_head branchCmp; exact hoare_liftAmbient (AmbientM.branchCmp _ _ _ _) _)
  | (rx_retention_head unsupported; exact hoare_liftAmbient (AmbientM.unsupported _) _)
  | rx_retention_step)
/-- Narrow local variant of Lifetimes.keypairPut_rest. The original
nullable-word/refcount failures and both immediate-unhash modes are retained. -/
theorem keypairPut_rest_getter_variant (key : Option KeypairId) (now : Bool) :
    SameView getterMetadata (keypairPut key now) := by
  intro initial
  change Preserves (fun g=>getterMetadata g=initial) _
  unfold keypairPut
  repeat' getter_cleanup_step initial
theorem retire_units (pid : PeerId) :
    SameView getterMetadata (retirePeerUnits pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a x v b run
  cases run
  rfl
/-- Narrow local variant of Lifetimes.peerPut_metadata. Final-release
deletion, packet/timer refusals and unit retirement remain actual source calls. -/
theorem peerPut_metadata_getter_variant (peer : Option PeerId) :
    SameView getterMetadata (peerPut peer) := by
  intro initial
  change Preserves (fun g=>getterMetadata g=initial) _
  unfold peerPut
  repeat' first
    | (rx_retention_head retirePeerUnits; exact (retire_units _).wp (fun s=>s=initial))
    | getter_cleanup_step initial
theorem keypairs_clear (pid : PeerId) :
    SameView getterMetadata (keypairsClear pid) := by
  intro initial
  change Preserves (fun g=>getterMetadata g=initial) _
  unfold keypairsClear
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  repeat' first
    | (rx_retention_head keypairPut; exact (keypairPut_rest_getter_variant _ _).wp (fun s=>s=initial))
    | getter_cleanup_step initial
theorem handshake_clear (pid : PeerId) :
    SameView getterMetadata (handshakeClear pid) := by
  intro initial
  change Preserves (fun g=>getterMetadata g=initial) _
  unfold handshakeClear handshakeZero
  repeat' getter_cleanup_step initial
theorem clear_worker (pid : PeerId) :
    SameView getterMetadata (queuedExpiredZeroKeyMaterial pid) :=
  (handshake_clear pid).bind (fun _=>(keypairs_clear pid).bind (fun _=>peerPut_metadata_getter_variant (some pid)))


theorem header_of_metadata {α : Type} {action : WG.M α}
    (frame : SameView getterMetadata action) :
    SameView (fun g=>g.dev.map sendConfiguration) action := by
  apply frame.of_factor (fun value=>value.map Prod.fst)
  intro g
  simp only [getterMetadata,Option.map_map,Function.comp_def]
theorem node_header {α : Type} {action : WG.M α} (frame : SameNode action) :
    SameView (fun g=>g.dev.map sendConfiguration) action := by
  apply frame.of_factor (fun store : WGStoreView=>store.dev.map sendConfiguration)
  intro g
  simp only [nodeView,nodeDevice,wgStoreView,Option.map_map,Function.comp_def]
  rfl
theorem header_contracts : AllowedFrame.Contracts (fun g=>g.dev.map sendConfiguration) where
  aip := fun action=>header_of_metadata (aip action)
  deleteList := fun id=>header_of_metadata (list_delete id)
  appendList := fun pid id=>header_of_metadata
    (modify_peer pid (fun p=>{p with allowedipsList:=p.allowedipsList++[id]}))
  sequence := header_of_metadata (modify_device _ (fun _=>rfl))
  removeNode := fun id=>node_header (removeNodeBody_sameNode id)
/-- Header projection of the existing generic allowed-IP factory, joined to
the existing exact socket/selector frame for the same normal original run. -/
theorem remove_allowed (pid : PeerId) : SameView getterMetadata (removeByPeer pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a result final after run
  have head := (ProjectedAction.iff_run_ambient _ _ _).mp
    (AllowedFrame.remove header_contracts pid) g a result final after run
  obtain ⟨sock,fixtures⟩ := removeByPeer_readbackFrame pid g.nlSock7 g.fixtureNetDevices
    g a result final after ⟨rfl,rfl⟩ run
  change final.dev.map sendConfiguration = g.dev.map sendConfiguration at head
  unfold getterMetadata
  rw [sock,fixtures]
  have project := congrArg (Option.map fun config=>(config,g.nlSock7,g.fixtureNetDevices)) head
  simpa only [Option.map_map,Function.comp_def] using project
theorem make_dead (pid : PeerId) : SameView getterMetadata (peerMakeDead pid) := by
  rw [peerMakeDead_source]
  intro initial
  change Preserves (fun g=>getterMetadata g=initial) _
  unfold makeDeadAfterRemoval
  repeat' first
    | (rx_retention_head removeByPeer; exact (remove_allowed _).wp (fun s=>s=initial))
    | getter_cleanup_step initial

end Leanux.Proofs.WG.Config.GetterCleanup
