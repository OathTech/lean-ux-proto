import Leanux.Proofs.WG.Packets.PublicationConsumeHistory
import Leanux.Proofs.WG.Origins.OwnerCompletion

/-! The published packet anchor survives normal receive completion. Peer
retention includes both immutable identity fields, independently of key validity;
release may delete peers. All source guards and recorded failures remain actual. -/
namespace Leanux.Proofs.WG.PublicationCompletion
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues CurrentIdentity
variable {initial : Option (PeerId → Option (Nat × Key))}

/-- Each surviving peer identity was present in the specified input view. -/
def PeersRetained (before : Option (PeerId → Option (Nat × Key))) (w : WGWorld) : Prop :=
  ∀ pid ident, (peerView w).bind (fun peers => peers pid) = some ident →
    before.bind (fun peers => peers pid) = some ident

theorem peers_refl (w : WGWorld) : PeersRetained (peerView w) w := fun _ _ h => h

theorem peers_trans (h : PeersRetained initial w) (g : PeersRetained (peerView w) v) :
    PeersRetained initial v := fun pid ident hv => h pid ident (g pid ident hv)

theorem peers_fields (h : PeersRetained (peerView w) v)
    (pid : PeerId) (d : Device) (p : Peer) (hd : v.dev = some d) (hp : d.peers[pid]? = some p) :
    ∃ old q, w.dev = some old ∧ old.peers[pid]? = some q ∧ identity p = identity q := by
  have old := h pid (identity p) (by simp only [peerView,hd,Option.map_some,Option.bind_some,hp])
  cases hw : w.dev with
  | none => simp [peerView,hw] at old
  | some before =>
    simp only [peerView,hw,Option.map_some,Option.bind_some] at old
    obtain ⟨q,hq,same⟩ := Option.map_eq_some_iff.mp old
    exact ⟨before,q,rfl,hq,same.symm⟩

private theorem exact_view {α : Type} {a : WG.M α}
    (ha : SameView peerView a) (initial) : Preserves (PeersRetained initial) a := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hi hr
  have hv := (ProjectedAction.iff_run_ambient _ _ _).mp ha w ambient result v ambient' hr
  simpa only [PeersRetained,hv] using hi

private theorem configured {α : Type} {a : WG.M α}
    (ha : SameView ConfiguredIdentity.view a) (initial) : Preserves (PeersRetained initial) a :=
  exact_view (peerView_of_configured ha) initial

private theorem fields_peer (w v : WGWorld) (d : Device) (hd : w.dev = some d)
    (fields : ∀ after, v.dev = some after → ∀ (pid : PeerId) (p : Peer), after.peers[pid]? = some p →
      ∃ old, d.peers[pid]? = some old ∧ identity p = identity old) :
    PeersRetained (peerView w) v := by
  intro pid ident hv
  cases hafter : v.dev with
  | none => simp [peerView,hafter] at hv
  | some after =>
    simp only [peerView,hafter,Option.map_some,Option.bind_some] at hv
    obtain ⟨p,hp,same⟩ := Option.map_eq_some_iff.mp hv
    obtain ⟨old,ho,identity⟩ := fields after hafter pid p hp
    simp only [peerView,hd,Option.map_some,Option.bind_some,ho,Option.map_some]
    exact congrArg some (identity.symm.trans same)

/-- Actual normal payment retains full identities of survivors, without a
positive-reference or live-key premise. The final arm may erase its peer. -/
theorem peerPut_peers (peer : Option PeerId) (initial) :
    Preserves (PeersRetained initial) (peerPut peer) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hi hr
  apply peers_trans hi
  cases result
  cases peer with
  | none =>
    simp [peerPut, branch, AmbientM.branch] at hr
    rcases hr with ⟨rfl, rfl⟩
    exact peers_refl _
  | some pid =>
    cases hd : w.dev with
    | none =>
      simp [peerPut, requireNotPending, getPeer, getDev, hd, branch, AmbientM.branch,
        invariant, AmbientM.invariant] at hr
      cases hr
    | some d =>
      cases hp : d.peers[pid]? with
      | none =>
        simp [peerPut, requireNotPending, getPeer, getDev, hd, hp, branch, AmbientM.branch,
          invariant, AmbientM.invariant] at hr
        cases hr
      | some p =>
        have hl (a : IndexM Unit) : (liftM a : WG.M Unit) = liftIndex a := rfl
        by_cases positive : 0 < p.refcount
        · have nonzero : p.refcount ≠ 0 := by omega
          by_cases final : p.refcount = 1
          all_goals
            simp [peerPut, requireNotPending, getPeer, getDev, setPeer, modifyDev,
              refcountDecAndTest, branch, branchCmp, indexRemove_eq, indexUnhash,
              hl, liftIndex_run, retirePeerUnits, modifyAmbient,
              CounterWindow.branch_run, CounterWindow.branchCmp_run,
              hd, hp, positive, nonzero, final,
              StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
              CounterWindow.except_ok_bind, CounterWindow.except_pure,
              invariant, AmbientM.invariant, unsupported, AmbientM.unsupported] at hr
          all_goals repeat' first | split at hr | contradiction
          all_goals rcases hr with ⟨rfl, rfl⟩
          all_goals apply fields_peer w _ d hd
          all_goals
            intro after ha
            cases ha
          all_goals
            intro q current resident
            by_cases eq : pid = q
            · subst q
              simp only [Std.TreeMap.getElem?_erase, Std.TreeMap.getElem?_insert,
                Std.LawfulEqOrd.compare_eq_iff_eq, ite_true] at resident
              first
                | contradiction
                | (cases resident; exact ⟨p, hp, rfl⟩)
            · exact ⟨current, by simpa [Std.TreeMap.getElem?_erase,
                Std.TreeMap.getElem?_insert, eq] using resident, rfl⟩
        · have zero : p.refcount = 0 := by omega
          simp [peerPut, requireNotPending, getPeer, getDev, setPeer, modifyDev,
            refcountDecAndTest, hd, hp,
            branch, branchCmp, CounterWindow.branch_run, CounterWindow.branchCmp_run,
            zero, StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
            CounterWindow.except_ok_bind, CounterWindow.except_pure,
            unsupported, AmbientM.unsupported] at hr
          cases hr

theorem read_bind (initial) {α : Type} (pid : PeerId) (f : Peer → WG.M α)
    (hf : ∀ p, initial.bind (fun peers => peers pid) = some (identity p) →
      Preserves (PeersRetained initial) (f p)) :
    Preserves (PeersRetained initial) (getPeer pid >>= f) := by
  apply hoare_bind _ _ (show Hoare (getPeer pid) (PeersRetained initial)
    (fun p w => PeersRetained initial w ∧ initial.bind (fun peers => peers pid) = some (identity p)) from ?_)
  · intro p
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b hi hr
    exact (hoare_iff_run_ambient _ _ _).mp (hf p hi.2) w a result v b hi.1 hr
  · apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a p v b hi hr
    obtain ⟨rfl,_,d,hd,hp⟩ := getPeer_normal pid w v p a b hr
    exact ⟨hi,hi pid (identity p) (by simp only [peerView,hd,Option.map_some,Option.bind_some,hp])⟩

theorem set_saved (initial) (pid : PeerId) (p : Peer)
    (hp : initial.bind (fun peers => peers pid) = some (identity p)) :
    Preserves (PeersRetained initial) (setPeer pid p) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi hr
  cases hr
  intro q ident hq
  cases hd : w.dev with
  | none => simp [peerView,hd] at hq
  | some d =>
    simp only [peerView,hd,Option.map_some,Option.bind_some,Std.TreeMap.getElem?_insert,
      Std.LawfulEqOrd.compare_eq_iff_eq] at hq
    by_cases eq : pid = q
    · subst q
      simp only [ite_true,Option.map_some,Option.some.injEq] at hq
      exact hq ▸ hp
    · simp only [ite_eq_right eq] at hq
      exact hi q ident (by simpa only [peerView,hd,Option.map_some,Option.bind_some] using hq)

private theorem peerGet_peers (pid : PeerId) (initial) :
    Preserves (PeersRetained initial) (peerGet pid) :=
  configured ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentTraffic.«0».Leanux.Proofs.WG.CurrentTraffic.peerGet_view) pid) initial

private theorem keypairGet_peers (kid : Option KeypairId) (initial) :
    Preserves (PeersRetained initial) (keypairGet kid) :=
  configured ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentTraffic.«0».Leanux.Proofs.WG.CurrentTraffic.keypairGet_view) kid) initial

private theorem modify_peers (f : Device → Device) (h : ∀ d, (f d).peers = d.peers) (initial) :
    Preserves (PeersRetained initial) (modifyDev f) := by
  apply exact_view
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b hr
  cases hr
  simp only [peerView,Option.map_map,Function.comp_def,h]

macro "publication_peer_step " initial:term : tactic => `(tactic| first
  | (env_bind_head getPeer; apply read_bind $initial; intro p hp)
  | (rx_retention_head setPeer; apply set_saved $initial; assumption)
  | (rx_retention_head peerPut; exact peerPut_peers _ $initial)
  | (rx_retention_head getPeer
     exact configured (ConfiguredIdentity.getPeer_view _) $initial)
  | (rx_retention_head getDev
     exact configured (ConfiguredIdentity.sameWG (project := id) getDev_sameWGStore) $initial)
  | (rx_retention_head peerGet
     exact peerGet_peers _ $initial)
  | (rx_retention_head keypairGet
     exact keypairGet_peers _ $initial)
  | (rx_retention_head getKeypair; exact configured (ConfiguredIdentity.getKeypair_view _) $initial)
  | (rx_retention_head setKeypair; exact configured (ConfiguredIdentity.setKeypair_view _ _) $initial)
  | (rx_retention_head keypairPut; exact configured (ConfiguredIdentity.keypairPut_view _ _) $initial)
  | (rx_retention_head branchExpired
     exact (branchExpired_sameWGWorld _ _ _ _).wp (PeersRetained $initial))
  | (rx_retention_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ _)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (rx_retention_head get; exact hoare_consequence (hoare_get _)
      (fun _ h => h) (fun _ _ h => h.2))
  | (rx_retention_head modifyDev
     apply modify_peers
     intro d; rfl)
  | (rx_retention_head modify; apply hoare_modify; intro w h; exact h)
  | (rx_retention_head ForIn.forIn
     apply list_view_spec id (PeersRetained $initial)
     intro x b
     change Preserves (PeersRetained $initial) _)
  | (rx_retention_head Functor.discard
     apply discard_view_spec id (PeersRetained $initial)
     change Preserves (PeersRetained $initial) _)
  | (first | rx_retention_head throw | rx_retention_head MonadExceptOf.throw
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a result v b hi hr
     cases hr)
  | rx_retention_step)

macro "publication_peer_skb" : tactic => `(tactic| first
  | (rx_retention_head getTxSkb; unfold getTxSkb)
  | (rx_retention_head setTxSkb; unfold setTxSkb)
  | (rx_retention_head newTxSkb; unfold newTxSkb)
  | (rx_retention_head freeTxSkb; unfold freeTxSkb)
  | (rx_retention_head liftSkb
     apply hoare_liftSkb
     intro w d store hi hd
     simpa only [PeersRetained,peerView,hd,Option.map_some] using hi))

private theorem sendQueued_peers (pid : PeerId) (retry : Bool) (initial) :
    Preserves (PeersRetained initial) (sendQueuedHandshakeInitiation pid retry) := by
  unfold sendQueuedHandshakeInitiation
  simp (config := {zeta := false}) only [branch,peekQueuedUnit,recordQueued]
  repeat' publication_peer_step initial

private theorem fresh_peers (pid : PeerId) (initial) :
    Preserves (PeersRetained initial) (keepKeyFreshRx pid) := by
  unfold keepKeyFreshRx WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head sendQueuedHandshakeInitiation; exact sendQueued_peers _ _ initial)
    | publication_peer_step initial

private theorem enqueue_peers (item : List SkbId) (state : PacketState) (initial) :
    Preserves (PeersRetained initial) (enqueuePerPeerTx item state) := by
  unfold enqueuePerPeerTx
  simp (config := {zeta := false}) only [peekQueuedUnit,recordQueued,invariant]
  repeat' first
    | (rx_retention_head cpumaskChooseOnline
       exact configured ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentTraffic.«0».Leanux.Proofs.WG.CurrentTraffic.cpumaskChooseOnline_view) _) initial)
    | publication_peer_skb
    | publication_peer_step initial

private theorem create_peers (pid : PeerId) (item : List SkbId) (initial) :
    Preserves (PeersRetained initial) (createData pid item) := by
  unfold createData
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head enqueuePerDeviceAndPeer
       exact configured ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentTraffic.«0».Leanux.Proofs.WG.CurrentTraffic.enqueuePerDeviceAndPeer_view) _ _) initial)
    | (rx_retention_head enqueuePerPeerTx; exact enqueue_peers _ _ initial)
    | publication_peer_skb
    | publication_peer_step initial

private theorem noKey_peers (pid : PeerId) (packets : List Packet)
    (keypair : Option KeypairId) (invalid : Bool) (initial) :
    Preserves (PeersRetained initial) (stagedOutNokey pid packets keypair invalid) := by
  have restore : SameView ConfiguredIdentity.view (do
      setPeer pid {(← getPeer pid) with staged := packets ++ (← getPeer pid).staged}) := by
    intro initial
    change Preserves (fun w => ConfiguredIdentity.view w = initial) _
    repeat' configured_step initial
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
    | (env_bind_head getPeer; exact configured restore initial)
    | (rx_retention_head sendQueuedHandshakeInitiation; exact sendQueued_peers _ _ initial)
    | publication_peer_step initial

private theorem submit_peers (pid kid : Nat) (packets : List DataPacket) (initial) :
    Preserves (PeersRetained initial) (RxCredits.stagedSubmit pid kid packets) := by
  unfold RxCredits.stagedSubmit Affiliation.sendAcquire
  repeat' first
    | (rx_retention_head createData; exact create_peers _ _ initial)
    | (rx_retention_head List.mapM
       apply mapM_view_spec id (PeersRetained initial)
       intro packet
       change Preserves (PeersRetained initial) _)
    | publication_peer_skb
    | publication_peer_step initial

private theorem keySource_peers (pid kid : Nat) (packets : List Packet) (initial) :
    Preserves (PeersRetained initial) (RxCredits.stagedKeySource pid kid packets) := by
  unfold RxCredits.stagedKeySource
  simp (config := {zeta := false}) only [branch,branchCmp]
  repeat' first
    | (rx_retention_head stagedOutNokey; exact noKey_peers _ _ _ _ initial)
    | (rx_retention_head RxCredits.stagedSubmit; exact submit_peers _ _ _ initial)
    | (rx_retention_head ipTunnelEcnEncap
       exact (ipTunnelEcnEncap_sameWGWorld _).wp (PeersRetained initial))
    | publication_peer_step initial

/-- Staged transmission can release a peer; every surviving identity is
retained, independently of sending/receiving key validity. -/
theorem sendStagedPackets_peers (pid : PeerId) (initial) :
    Preserves (PeersRetained initial) (sendStagedPackets pid) := by
  rw [← RxCredits.stagedFullSource_eq]
  unfold RxCredits.stagedFullSource
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head stagedOutNokey; exact noKey_peers _ _ _ _ initial)
    | (rx_retention_head RxCredits.stagedKeySource; exact keySource_peers _ _ _ initial)
    | publication_peer_step initial

/-- Full peer identity retention through the actual completion, including
its staged-send and lookup repayment paths. No live-key condition is used. -/
theorem consumeDataDone_peers (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) (initial) :
    Preserves (PeersRetained initial) (consumeDataDone pid pkt endpoint) := by
  unfold consumeDataDone WG.andM WG.orM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head setPeerEndpoint
       exact configured (ConfiguredReceiveLeaves.setPeerEndpoint_view _ _) initial)
    | (rx_retention_head receivedWithKeypair
       exact configured ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentTraffic.«0».Leanux.Proofs.WG.CurrentTraffic.receivedWithKeypair_view) _ _) initial)
    | (rx_retention_head sendStagedPackets; exact sendStagedPackets_peers _ initial)
    | (rx_retention_head keepKeyFreshRx; exact fresh_peers _ initial)
    | (rx_retention_head timersHandshakeComplete
       exact configured (ConfiguredReceiveLeaves.timersHandshakeComplete_view _ _) initial)
    | (rx_retention_head timersAnyAuthenticatedPacketReceived
       exact configured (ConfiguredReceiveLeaves.timersAnyAuthenticatedPacketReceived_view _) initial)
    | (rx_retention_head timersTraversal
       exact configured (ConfiguredIdentity.timersTraversal_view _) initial)
    | (rx_retention_head timersDataReceived
       exact configured (ConfiguredReceiveLeaves.timersDataReceived_view _) initial)
    | (rx_retention_head updateRxStats
       exact configured ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentRx.«0».Leanux.Proofs.WG.CurrentRx.updateRxStats_view) _ _) initial)
    | (rx_retention_head dishonest
       exact configured ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentRx.«0».Leanux.Proofs.WG.CurrentRx.dishonest_view) _) initial)
    | (rx_retention_head lookupSrc
       exact configured ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentRx.«0».Leanux.Proofs.WG.CurrentRx.lookupSrc_view) _ _) initial)
    | (rx_retention_head inetEcnDecapsulate
       exact configured (ConfiguredIdentity.sameWG (project := id)
         (inetEcnDecapsulate_sameWGStore _ _ _)) initial)
    | publication_peer_step initial

/-- A concrete exact packet-store frame and deletion-permitting peer
retention transport the existing same-witness publication invariant. -/
theorem preserves_of_frames {α : Type} (a : WG.M α)
    (rx : SameView RxDisposition.nativeRxStore a)
    (peers : ∀ initial, Preserves (PeersRetained initial) a)
    (history : List RxHistory.Event) : Preserves (PublicationHistory.Inv history) a := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hi hr
  have store := (ProjectedAction.iff_run_ambient _ _ _).mp rx w ambient result v ambient' hr
  have retained := (hoare_iff_run_ambient _ _ _).mp (peers (peerView w))
    w ambient result v ambient' (peers_refl w) hr
  apply hi.transport
  · intro id pkt hp _
    refine ⟨?_,?_⟩
    · exact (congrFun (congrArg Prod.snd store) id).symm.trans hp
    · exact congrArg (fun epoch : Option Nat => (epoch.getD 0,id+1)) (congrArg Prod.fst store)
  · exact peers_fields retained

/-- Completion changes local bytes and may erase peers, but leaves stored
RX packet identities intact. Certificates remain anchored to the same earlier
publication, with residency required only by the actual later consume getter. -/
theorem consumeDataDone_preserves (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint)
    (history : List RxHistory.Event) :
    Preserves (PublicationHistory.Inv history) (consumeDataDone pid pkt endpoint) := by
  apply preserves_of_frames
  · exact ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.done_geometry) pid pkt endpoint).factor Prod.snd
  · exact consumeDataDone_peers pid pkt endpoint

end Leanux.Proofs.WG.PublicationCompletion
