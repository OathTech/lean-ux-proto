import Leanux.Proofs.WG.Origins.ConfiguredRemoval
import Leanux.Proofs.WG.Origins.CurrentTraffic
import Leanux.Proofs.WG.Queues.CreationLoan

/-! Standalone configured-registry preservation through native staged sends.
Only existing configured identity is required; final release may erase peers. -/
namespace Leanux.Proofs.WG.ConfiguredTraffic
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues ConfiguredRemoval ConfiguredHandshake ConfiguredReceive

private theorem update (pid : PeerId) (f : Peer → Peer)
    (same : ∀ p, ConfiguredIdentity.cell (f p)=ConfiguredIdentity.cell p) :
    Preserves ConfiguredIdentity.Inv (getPeer pid >>= fun p => setPeer pid (f p)) :=
  frame (ConfiguredIdentity.modifyPeer_view pid f same)

private theorem updateThen (pid : PeerId) (f : Peer → Peer) (tail : Unit → WG.M α)
    (same : ∀ p, ConfiguredIdentity.cell (f p)=ConfiguredIdentity.cell p)
    (next : ∀ x, Preserves ConfiguredIdentity.Inv (tail x)) :
    Preserves ConfiguredIdentity.Inv (getPeer pid >>= fun p => setPeer pid (f p) >>= tail) := by
  simpa only [bind_assoc] using preserves_bind (update pid f same) next

private theorem keyUpdateThen (kid : KeypairId) (f : Keypair → Keypair)
    (next : Keypair → WG.M α) (hn : ∀ k, Preserves ConfiguredIdentity.Inv (next k)) :
    Preserves ConfiguredIdentity.Inv (do let k ← getKeypair kid; setKeypair kid (f k); next k) :=
  preserves_bind (frame (ConfiguredIdentity.getKeypair_view kid)) (fun k =>
    preserves_bind (frame (ConfiguredIdentity.setKeypair_view kid (f k))) (fun _ => hn k))

private theorem keyUpdate (kid : KeypairId) (f : Keypair → Keypair) :
    Preserves ConfiguredIdentity.Inv (getKeypair kid >>= fun k => setKeypair kid (f k)) :=
  preserves_bind (frame (ConfiguredIdentity.getKeypair_view kid)) (fun k =>
    frame (ConfiguredIdentity.setKeypair_view kid (f k)))

macro "configured_traffic_key" : tactic => `(tactic| first
  | (current_key_update_head setKeypair; exact keyUpdate _ _)
  | (current_key_update_head Bind.bind; apply keyUpdateThen; intro k))

private theorem skb (action : SkbM α) : Preserves ConfiguredIdentity.Inv (liftSkb action) := by
  apply frame
  intro initial
  apply hoare_liftSkb
  intro w d store hi hd
  simpa only [ConfiguredIdentity.view,hd,Option.map_some,ConfiguredIdentity.state] using hi

private theorem keyGet (kp : Option KeypairId) : Preserves ConfiguredIdentity.Inv (keypairGet kp) :=
  frame ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentTraffic.«0».Leanux.Proofs.WG.CurrentTraffic.keypairGet_view) kp)

macro "configured_traffic_step" : tactic => `(tactic| first
  | (receive_update_head setPeer; apply update; intro p; rfl)
  | (receive_update_head Bind.bind
     apply updateThen
     · intro p; rfl
     intro x)
  | configured_traffic_key
  | (rx_retention_head peerGet; exact frame (RxCredits.CreationLoan.peerGet_configured_view _))
  | (rx_retention_head peerPut; exact ConfiguredIdentity.peerPut_preserves _)
  | (rx_retention_head keypairGet; exact keyGet _)
  | (rx_retention_head keypairPut; exact frame (ConfiguredIdentity.keypairPut_view _ _))
  | (rx_retention_head getKeypair; exact frame (ConfiguredIdentity.getKeypair_view _))
  | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp ConfiguredIdentity.Inv)
  | (rx_retention_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ ConfiguredIdentity.Inv)
  | (rx_retention_head getTxSkb; unfold getTxSkb)
  | (rx_retention_head setTxSkb; unfold setTxSkb)
  | (rx_retention_head newTxSkb; unfold newTxSkb)
  | (rx_retention_head freeTxSkb; unfold freeTxSkb)
  | (rx_retention_head liftSkb; exact skb _)
  | configured_removal_step)

theorem queued (pid : PeerId) (retry : Bool) :
    Preserves ConfiguredIdentity.Inv (sendQueuedHandshakeInitiation pid retry) := by
  unfold sendQueuedHandshakeInitiation
  simp (config := {zeta := false}) only [branch,peekQueuedUnit,recordQueued]
  repeat' configured_traffic_step

private theorem enqueue (item : List SkbId) (state : PacketState) :
    Preserves ConfiguredIdentity.Inv (enqueuePerPeerTx item state) := by
  unfold enqueuePerPeerTx
  simp (config := {zeta := false}) only [peekQueuedUnit,recordQueued,invariant]
  repeat' first
    | (rx_retention_head cpumaskChooseOnline
       exact frame ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentTraffic.«0».Leanux.Proofs.WG.CurrentTraffic.cpumaskChooseOnline_view) _))
    | configured_traffic_step

private theorem create (pid : PeerId) (item : List SkbId) :
    Preserves ConfiguredIdentity.Inv (createData pid item) := by
  unfold createData
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head enqueuePerDeviceAndPeer
       exact frame ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentTraffic.«0».Leanux.Proofs.WG.CurrentTraffic.enqueuePerDeviceAndPeer_view) _ _))
    | (rx_retention_head enqueuePerPeerTx; exact enqueue _ _)
    | configured_traffic_step

private theorem restore (pid : PeerId) (packets : List Packet) :
    Preserves ConfiguredIdentity.Inv (do
      setPeer pid {(← getPeer pid) with staged := packets ++ (← getPeer pid).staged}) := by
  apply frame
  intro initial
  change Preserves (fun w => ConfiguredIdentity.view w=initial) _
  repeat' configured_step initial

private theorem outNokey (pid : PeerId) (packets : List Packet)
    (keypair : Option KeypairId) (invalid : Bool) :
    Preserves ConfiguredIdentity.Inv (stagedOutNokey pid packets keypair invalid) := by
  have factor : stagedOutNokey pid packets keypair invalid = (do
      if invalid then
        let some id := keypair | invariant "unreachable"
        let k ← getKeypair id
        setKeypair id {k with sending := {k.sending with isValid := false}}
      keypairPut keypair false
      for _ in packets do _ ← branch .stagedOrphanWalk true
      _ ← branch .stagedOrphanWalk false
      (do setPeer pid {(← getPeer pid) with staged := packets ++ (← getPeer pid).staged})
      sendQueuedHandshakeInitiation pid false) := by
    cases invalid <;> cases keypair <;>
      simp only [stagedOutNokey,Bool.false_eq_true,ite_false,ite_true,bind_assoc]
  rw [factor]
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (env_bind_head getPeer; exact restore pid packets)
    | (rx_retention_head sendQueuedHandshakeInitiation; exact queued _ _)
    | configured_traffic_step

private theorem submit (pid kid : Nat) (packets : List DataPacket) :
    Preserves ConfiguredIdentity.Inv (RxCredits.stagedSubmit pid kid packets) := by
  unfold RxCredits.stagedSubmit Affiliation.sendAcquire
  repeat' first
    | (rx_retention_head createData; exact create _ _)
    | (rx_retention_head List.mapM
       apply mapM_view_spec id ConfiguredIdentity.Inv
       intro packet
       change Preserves ConfiguredIdentity.Inv _)
    | configured_traffic_step

private theorem keySource (pid kid : Nat) (packets : List Packet) :
    Preserves ConfiguredIdentity.Inv (RxCredits.stagedKeySource pid kid packets) := by
  unfold RxCredits.stagedKeySource
  simp (config := {zeta := false}) only [branch,branchCmp]
  repeat' first
    | (rx_retention_head stagedOutNokey; exact outNokey _ _ _ _)
    | (rx_retention_head RxCredits.stagedSubmit; exact submit _ _ _)
    | (rx_retention_head ipTunnelEcnEncap; exact (ipTunnelEcnEncap_sameWGWorld _).wp ConfiguredIdentity.Inv)
    | configured_traffic_step

theorem readPeer (pid : PeerId) : Hoare (getPeer pid) ConfiguredIdentity.Inv
    (fun p w => ConfiguredIdentity.Inv w ∧
      (ConfiguredIdentity.view w).bind (fun s => s.peers pid)=some (ConfiguredIdentity.cell p)) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b hi run
  have eq := (Peers.getPeer_current pid w v p a b run).1
  exact ⟨eq ▸ hi,((hoare_iff_run_ambient _ _ _).mp
    (ConfiguredIdentity.getPeer_spec (fun _ => True) pid) w a p v b trivial run).2⟩

theorem writePeer (pid : PeerId) (p : Peer) : Hoare (setPeer pid p)
    (fun w => ConfiguredIdentity.Inv w ∧
      (ConfiguredIdentity.view w).bind (fun s => s.peers pid)=some (ConfiguredIdentity.cell p))
    (fun _ => ConfiguredIdentity.Inv) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  have eq := (hoare_iff_run_ambient _ _ _).mp
    (ConfiguredIdentity.setPeer_spec (fun s => s=ConfiguredIdentity.view w) pid p)
      w a result v b ⟨rfl,hi.2⟩ run
  intro s hs
  exact hi.1 s (eq.symm.trans hs)

theorem staged (pid : PeerId) :
    Preserves (ConfiguredIdentity.Inv) (sendStagedPackets pid) := by
  rw [← RxCredits.stagedFullSource_eq]
  unfold RxCredits.stagedFullSource
  apply hoare_bind _ _ (readPeer pid)
  intro p
  apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .stagedEmpty p.staged.isEmpty) _)
  intro empty
  cases empty with
  | true =>
    exact hoare_consequence (preserves_pure ()) (fun _ h => h.1) (fun _ _ h => h)
  | false =>
    apply hoare_bind _ _ (writePeer pid {p with staged := []})
    intro _
    change Preserves (ConfiguredIdentity.Inv) _
    simp (config := {zeta := false}) only [branch,invariant]
    repeat' first
      | (rx_retention_head stagedOutNokey; exact outNokey _ _ _ _)
      | (rx_retention_head RxCredits.stagedKeySource; exact keySource _ _ _)
      | configured_traffic_step

theorem keepalive (pid : PeerId) :
    Preserves (ConfiguredIdentity.Inv) (sendKeepalive pid) := by
  unfold sendKeepalive
  apply hoare_bind _ _ (readPeer pid)
  intro p
  let P := fun w => ConfiguredIdentity.Inv w ∧
    (ConfiguredIdentity.view w).bind (fun s => s.peers pid) = some (ConfiguredIdentity.cell p)
  apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .keepaliveStagedEmpty p.staged.isEmpty) P)
  intro empty
  cases empty with
  | false =>
    change Hoare (sendStagedPackets pid) P (fun _ => ConfiguredIdentity.Inv)
    exact hoare_consequence (staged pid)
      (fun _ h => h.1) (fun _ _ h => h)
  | true =>
    dsimp only
    apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.hiddenAlloc .keepaliveSkb) P)
    intro allocated
    apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .keepaliveNoMem (!allocated)) P)
    intro absent
    cases absent with
    | true =>
      exact hoare_consequence (preserves_pure ()) (fun _ h => h.1) (fun _ _ h => h)
    | false =>
      have getter : Preserves P getDev := by
        unfold getDev
        simp only [invariant]
        repeat' first
          | (rx_retention_head get; exact hoare_consequence (hoare_get P)
              (fun _ h => h) (fun _ _ h => h.2))
          | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ P)
          | rx_retention_step
      apply hoare_bind _ _ getter
      intro d
      apply hoare_bind _ _ (writePeer pid {p with staged := p.staged ++ [{mtu := d.mtu}]})
      intro _
      exact staged pid


end Leanux.Proofs.WG.ConfiguredTraffic
