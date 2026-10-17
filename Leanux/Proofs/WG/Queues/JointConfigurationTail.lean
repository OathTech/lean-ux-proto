import Leanux.Proofs.WG.Queues.JointConfiguration
import Leanux.Proofs.WG.Configuration.PeerTailCompletion

/-! Exact completion and lifetime projections through the actual final
configuration actions. Append facts describe journals on both return and Stop;
they impose no lifetime, allocation, or routing invariant. -/
namespace Leanux.Proofs.WG.Queues.RoutingJoint
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes AllowedIps Configuration

private theorem append_ite {α : Type} (p : Prop) [Decidable p] {a b : MixedM α}
    (ha : p → StateAppends a) (hb : ¬p → StateAppends b) :
    StateAppends (if p then a else b) := by
  by_cases h : p
  · simpa only [h,ite_true] using ha h
  · simpa only [h,ite_false] using hb h

theorem stateAppends_forIn {α β : Type} (xs : List α) (initial : β)
    (body : α → β → MixedM (ForInStep β)) (hb : ∀ x b, StateAppends (body x b)) :
    StateAppends (forIn xs initial body) := by
  induction xs generalizing initial with
  | nil => exact StateAppends.pure initial
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply (hb x initial).bind
    intro step
    cases step with
    | done b => exact StateAppends.pure b
    | yield b => exact ih b

private theorem append_mapM {α β : Type} (xs : List α) (f : α → MixedM β)
    (hf : ∀ x, StateAppends (f x)) : StateAppends (xs.mapM f) := by
  induction xs with
  | nil => exact StateAppends.pure []
  | cons x xs ih =>
    rw [List.mapM_cons]
    exact (hf x).bind (fun _ => ih.bind (fun _ => StateAppends.pure _))

private theorem readKey_appends (id : KeypairId) : StateAppends (getKeypairPrefix id) := by
  intro w ambient h
  change ∃ s, (runStatePrefix (getKeypairPrefix id) w ambient h).2 = h ++ s
  rw [getKeypairPrefix_run]
  cases ((getKeypair id).run w).run ambient with
  | error e => exact ⟨[],(List.append_nil _).symm⟩
  | ok out => exact ⟨_,rfl⟩

private theorem writeKey_appends (id : KeypairId) (key : Keypair) : StateAppends (setKeypairPrefix id key) := by
  intro w ambient h
  change ∃ s, (if w.dev.isSome then h ++ _ else h) = h ++ s
  split
  · exact ⟨_,rfl⟩
  · exact ⟨[],(List.append_nil _).symm⟩

private theorem readPacket_appends (id : SkbId) : StateAppends (getTxSkbPrefix id) := by
  intro w ambient h
  change ∃ s, (runStatePrefix (getTxSkbPrefix id) w ambient h).2 = h ++ s
  rw [getTxSkbPrefix_run]
  cases ((getTxSkb id).run w).run ambient with
  | error e => exact ⟨[],(List.append_nil _).symm⟩
  | ok out => exact ⟨_,rfl⟩

private theorem writePacket_appends (id : SkbId) (packet : DataPacket) : StateAppends (writeTxSkbPrefix id packet) := by
  intro w ambient h
  change ∃ s, (if w.dev.isSome then h ++ _ else h) = h ++ s
  split
  · exact ⟨_,rfl⟩
  · exact ⟨[],(List.append_nil _).symm⟩

private theorem newPacket_appends (packet : DataPacket) : StateAppends (newTxSkbPrefix packet) := by
  intro w ambient h
  change ∃ s, (runStatePrefix (PacketAllocation.tx packet).observed w ambient h).2 = h ++ s
  rw [PacketAllocation.observation]
  cases (((PacketAllocation.tx packet).original).run w).run ambient with
  | error e => exact ⟨[],(List.append_nil _).symm⟩
  | ok out => exact ⟨_,rfl⟩

private theorem eraseKey_appends (id stamp : Nat) : StateAppends (eraseKeypairPrefix id stamp) :=
  fun _ _ _ => ⟨_,rfl⟩

private theorem erasePacket_appends (slot : Packets.Slot) : StateAppends (erasePacketPrefix slot) :=
  fun _ _ _ => ⟨_,rfl⟩

private theorem deref_appends (owner : IndexOwner) : StateAppends (peerDerefPrefix owner) := by
  unfold peerDerefPrefix
  apply StateAppends.bind
  · cases owner with
    | handshake pid => exact (StateAppends.focus _ _ _).bind (fun _ => StateAppends.pure _)
    | keypair id => exact (readKey_appends id).bind (fun _ => StateAppends.pure _)
  · intro peer
    cases peer
    · exact StateAppends.lift _
    · exact StateAppends.pure _

private theorem keyPut_appends (kp : Option KeypairId) (now : Bool) :
    StateAppends (keypairPutPrefix kp now) := by
  have rem (id : KeypairId) : StateAppends (removeKeypairEntryPrefix id) :=
    (deref_appends _).bind (fun _ => StateAppends.lift _)
  have lifted {α : Type} (a : WG.M α) : StateAppends (liftWGPrefix a : MixedM α) := StateAppends.lift a
  unfold keypairPutPrefix
  repeat' first
    | with_reducible exact readKey_appends _
    | with_reducible exact writeKey_appends _ _
    | with_reducible exact eraseKey_appends _ _
    | with_reducible exact rem _
    | with_reducible exact lifted _
    | with_reducible exact StateAppends.pure _
    | with_reducible apply StateAppends.bind
    | with_reducible apply append_ite
    | (maintenance_intro; try dsimp only)
    | split

private theorem queued_appends (pid : PeerId) (retry : Bool) :
    StateAppends (sendQueuedHandshakeInitiationPrefix pid retry) := by
  have lifted {α : Type} (a : WG.M α) : StateAppends (liftWGPrefix a : MixedM α) := StateAppends.lift a
  have read (id : PeerId) : StateAppends (getPeerMixed id) := StateAppends.focus _ _ _
  have write (id : PeerId) (p : Peer) : StateAppends (setPeerMixed id p) := StateAppends.focus _ _ _
  have acquire (id : PeerId) : StateAppends (peerGetMixed id) := StateAppends.focus _ _ _
  have put (id : Option PeerId) : StateAppends (peerPutMixed id) := StateAppends.focus _ _ _
  unfold sendQueuedHandshakeInitiationPrefix modifyPeerKeysPrefix
  repeat' first
    | with_reducible exact read _
    | with_reducible exact write _ _
    | with_reducible exact acquire _
    | with_reducible exact put _
    | with_reducible exact lifted _
    | with_reducible exact StateAppends.pure _
    | with_reducible apply StateAppends.bind
    | with_reducible apply append_ite
    | (maintenance_intro; try dsimp only)
    | split

private theorem noKey_appends (pid : PeerId) (packets : List Packet) (kp : Option KeypairId)
    (invalid : Bool) : StateAppends (stagedOutNokeyPrefix pid packets kp invalid) := by
  have lifted {α : Type} (a : WG.M α) : StateAppends (liftWGPrefix a : MixedM α) := StateAppends.lift a
  have read (id : PeerId) : StateAppends (getPeerMixed id) := StateAppends.focus _ _ _
  have write (id : PeerId) (p : Peer) : StateAppends (setPeerMixed id p) := StateAppends.focus _ _ _
  unfold stagedOutNokeyPrefix
  repeat' first
    | with_reducible exact readKey_appends _
    | with_reducible exact writeKey_appends _ _
    | with_reducible exact keyPut_appends _ _
    | with_reducible exact queued_appends _ _
    | with_reducible exact read _
    | with_reducible exact write _ _
    | with_reducible exact lifted _
    | with_reducible exact StateAppends.pure _
    | with_reducible apply stateAppends_forIn
    | with_reducible apply StateAppends.bind
    | with_reducible apply append_ite
    | (maintenance_intro; try dsimp only)
    | split

private theorem keyGet_appends (kp : Option KeypairId) : StateAppends (keypairGetPrefix kp) := by
  have lifted {α : Type} (a : WG.M α) : StateAppends (liftWGPrefix a : MixedM α) := StateAppends.lift a
  have read (id : PeerId) : StateAppends (getPeerMixed id) := StateAppends.focus _ _ _
  have write (id : PeerId) (p : Peer) : StateAppends (setPeerMixed id p) := StateAppends.focus _ _ _
  have acquire (id : PeerId) : StateAppends (peerGetMixed id) := StateAppends.focus _ _ _
  have put (id : Option PeerId) : StateAppends (peerPutMixed id) := StateAppends.focus _ _ _
  unfold keypairGetPrefix
  repeat' first
    | with_reducible exact read _
    | with_reducible exact write _ _
    | with_reducible exact acquire _
    | with_reducible exact put _
    | with_reducible exact readKey_appends _
    | with_reducible exact writeKey_appends _ _
    | with_reducible exact readPacket_appends _
    | with_reducible exact writePacket_appends _ _
    | with_reducible exact newPacket_appends _
    | with_reducible exact erasePacket_appends _
    | with_reducible exact keyPut_appends _ _
    | with_reducible exact deref_appends _
    | with_reducible exact queued_appends _ _
    | with_reducible exact noKey_appends _ _ _ _
    | with_reducible exact lifted _
    | with_reducible exact StateAppends.pure _
    | with_reducible apply append_mapM
    | with_reducible apply stateAppends_forIn
    | with_reducible apply StateAppends.bind
    | with_reducible apply append_ite
    | (maintenance_intro; try dsimp only)
    | split

private theorem cpu_appends (pid : PeerId) : StateAppends (cpumaskChooseOnlinePrefix pid) := by
  have lifted {α : Type} (a : WG.M α) : StateAppends (liftWGPrefix a : MixedM α) := StateAppends.lift a
  have read (id : PeerId) : StateAppends (getPeerMixed id) := StateAppends.focus _ _ _
  have write (id : PeerId) (p : Peer) : StateAppends (setPeerMixed id p) := StateAppends.focus _ _ _
  have acquire (id : PeerId) : StateAppends (peerGetMixed id) := StateAppends.focus _ _ _
  have put (id : Option PeerId) : StateAppends (peerPutMixed id) := StateAppends.focus _ _ _
  unfold cpumaskChooseOnlinePrefix
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | with_reducible exact read _
    | with_reducible exact write _ _
    | with_reducible exact acquire _
    | with_reducible exact put _
    | with_reducible exact readKey_appends _
    | with_reducible exact writeKey_appends _ _
    | with_reducible exact readPacket_appends _
    | with_reducible exact writePacket_appends _ _
    | with_reducible exact newPacket_appends _
    | with_reducible exact erasePacket_appends _
    | with_reducible exact keyPut_appends _ _
    | with_reducible exact deref_appends _
    | with_reducible exact queued_appends _ _
    | with_reducible exact noKey_appends _ _ _ _
    | with_reducible exact lifted _
    | with_reducible exact StateAppends.pure _
    | with_reducible apply append_mapM
    | with_reducible apply stateAppends_forIn
    | with_reducible apply StateAppends.bind
    | with_reducible apply append_ite
    | (maintenance_intro; try dsimp only)
    | split

private theorem enqueuePeer_appends (item : List SkbId) (state : PacketState) : StateAppends (enqueuePerPeerTxPrefix item state) := by
  have lifted {α : Type} (a : WG.M α) : StateAppends (liftWGPrefix a : MixedM α) := StateAppends.lift a
  have read (id : PeerId) : StateAppends (getPeerMixed id) := StateAppends.focus _ _ _
  have write (id : PeerId) (p : Peer) : StateAppends (setPeerMixed id p) := StateAppends.focus _ _ _
  have acquire (id : PeerId) : StateAppends (peerGetMixed id) := StateAppends.focus _ _ _
  have put (id : Option PeerId) : StateAppends (peerPutMixed id) := StateAppends.focus _ _ _
  unfold enqueuePerPeerTxPrefix setTxSkbPrefix
  repeat' first
    | with_reducible exact cpu_appends _
    | with_reducible exact read _
    | with_reducible exact write _ _
    | with_reducible exact acquire _
    | with_reducible exact put _
    | with_reducible exact readKey_appends _
    | with_reducible exact writeKey_appends _ _
    | with_reducible exact readPacket_appends _
    | with_reducible exact writePacket_appends _ _
    | with_reducible exact newPacket_appends _
    | with_reducible exact erasePacket_appends _
    | with_reducible exact keyPut_appends _ _
    | with_reducible exact deref_appends _
    | with_reducible exact queued_appends _ _
    | with_reducible exact noKey_appends _ _ _ _
    | with_reducible exact lifted _
    | with_reducible exact StateAppends.pure _
    | with_reducible apply append_mapM
    | with_reducible apply stateAppends_forIn
    | with_reducible apply StateAppends.bind
    | with_reducible apply append_ite
    | (maintenance_intro; try dsimp only)
    | split

private theorem enqueueBoth_appends (pid : PeerId) (item : List SkbId) : StateAppends (enqueuePerDeviceAndPeerPrefix pid item) := by
  have lifted {α : Type} (a : WG.M α) : StateAppends (liftWGPrefix a : MixedM α) := StateAppends.lift a
  have read (id : PeerId) : StateAppends (getPeerMixed id) := StateAppends.focus _ _ _
  have write (id : PeerId) (p : Peer) : StateAppends (setPeerMixed id p) := StateAppends.focus _ _ _
  have acquire (id : PeerId) : StateAppends (peerGetMixed id) := StateAppends.focus _ _ _
  have put (id : Option PeerId) : StateAppends (peerPutMixed id) := StateAppends.focus _ _ _
  unfold enqueuePerDeviceAndPeerPrefix setTxSkbPrefix
  repeat' first
    | with_reducible exact read _
    | with_reducible exact write _ _
    | with_reducible exact acquire _
    | with_reducible exact put _
    | with_reducible exact readKey_appends _
    | with_reducible exact writeKey_appends _ _
    | with_reducible exact readPacket_appends _
    | with_reducible exact writePacket_appends _ _
    | with_reducible exact newPacket_appends _
    | with_reducible exact erasePacket_appends _
    | with_reducible exact keyPut_appends _ _
    | with_reducible exact deref_appends _
    | with_reducible exact queued_appends _ _
    | with_reducible exact noKey_appends _ _ _ _
    | with_reducible exact lifted _
    | with_reducible exact StateAppends.pure _
    | with_reducible apply append_mapM
    | with_reducible apply stateAppends_forIn
    | with_reducible apply StateAppends.bind
    | with_reducible apply append_ite
    | (maintenance_intro; try dsimp only)
    | split

private theorem createData_appends (pid : PeerId) (item : List SkbId) : StateAppends (createDataPrefix pid item) := by
  have lifted {α : Type} (a : WG.M α) : StateAppends (liftWGPrefix a : MixedM α) := StateAppends.lift a
  have read (id : PeerId) : StateAppends (getPeerMixed id) := StateAppends.focus _ _ _
  have write (id : PeerId) (p : Peer) : StateAppends (setPeerMixed id p) := StateAppends.focus _ _ _
  have acquire (id : PeerId) : StateAppends (peerGetMixed id) := StateAppends.focus _ _ _
  have put (id : Option PeerId) : StateAppends (peerPutMixed id) := StateAppends.focus _ _ _
  unfold createDataPrefix freeTxSkbPrefix
  repeat' first
    | with_reducible exact enqueuePeer_appends _ _
    | with_reducible exact enqueueBoth_appends _ _
    | with_reducible exact read _
    | with_reducible exact write _ _
    | with_reducible exact acquire _
    | with_reducible exact put _
    | with_reducible exact readKey_appends _
    | with_reducible exact writeKey_appends _ _
    | with_reducible exact readPacket_appends _
    | with_reducible exact writePacket_appends _ _
    | with_reducible exact newPacket_appends _
    | with_reducible exact erasePacket_appends _
    | with_reducible exact keyPut_appends _ _
    | with_reducible exact deref_appends _
    | with_reducible exact queued_appends _ _
    | with_reducible exact noKey_appends _ _ _ _
    | with_reducible exact lifted _
    | with_reducible exact StateAppends.pure _
    | with_reducible apply append_mapM
    | with_reducible apply stateAppends_forIn
    | with_reducible apply StateAppends.bind
    | with_reducible apply append_ite
    | (maintenance_intro; try dsimp only)
    | split

private theorem staged_appends (pid : PeerId) : StateAppends (sendStagedPacketsPrefix pid) := by
  have lifted {α : Type} (a : WG.M α) : StateAppends (liftWGPrefix a : MixedM α) := StateAppends.lift a
  have read (id : PeerId) : StateAppends (getPeerMixed id) := StateAppends.focus _ _ _
  have write (id : PeerId) (p : Peer) : StateAppends (setPeerMixed id p) := StateAppends.focus _ _ _
  have acquire (id : PeerId) : StateAppends (peerGetMixed id) := StateAppends.focus _ _ _
  have put (id : Option PeerId) : StateAppends (peerPutMixed id) := StateAppends.focus _ _ _
  unfold sendStagedPacketsPrefix
  repeat' first
    | with_reducible exact keyGet_appends _
    | with_reducible exact createData_appends _ _
    | with_reducible exact read _
    | with_reducible exact write _ _
    | with_reducible exact acquire _
    | with_reducible exact put _
    | with_reducible exact readKey_appends _
    | with_reducible exact writeKey_appends _ _
    | with_reducible exact readPacket_appends _
    | with_reducible exact writePacket_appends _ _
    | with_reducible exact newPacket_appends _
    | with_reducible exact erasePacket_appends _
    | with_reducible exact keyPut_appends _ _
    | with_reducible exact deref_appends _
    | with_reducible exact queued_appends _ _
    | with_reducible exact noKey_appends _ _ _ _
    | with_reducible exact lifted _
    | with_reducible exact StateAppends.pure _
    | with_reducible apply append_mapM
    | with_reducible apply stateAppends_forIn
    | with_reducible apply StateAppends.bind
    | with_reducible apply append_ite
    | (maintenance_intro; try dsimp only)
    | split

private theorem keepalive_appends (pid : PeerId) : StateAppends (sendKeepalivePrefix pid) := by
  have lifted {α : Type} (a : WG.M α) : StateAppends (liftWGPrefix a : MixedM α) := StateAppends.lift a
  have read (id : PeerId) : StateAppends (getPeerMixed id) := StateAppends.focus _ _ _
  have write (id : PeerId) (p : Peer) : StateAppends (setPeerMixed id p) := StateAppends.focus _ _ _
  have acquire (id : PeerId) : StateAppends (peerGetMixed id) := StateAppends.focus _ _ _
  have put (id : Option PeerId) : StateAppends (peerPutMixed id) := StateAppends.focus _ _ _
  unfold sendKeepalivePrefix
  repeat' first
    | with_reducible exact staged_appends _
    | with_reducible exact read _
    | with_reducible exact write _ _
    | with_reducible exact acquire _
    | with_reducible exact put _
    | with_reducible exact readKey_appends _
    | with_reducible exact writeKey_appends _ _
    | with_reducible exact readPacket_appends _
    | with_reducible exact writePacket_appends _ _
    | with_reducible exact newPacket_appends _
    | with_reducible exact erasePacket_appends _
    | with_reducible exact keyPut_appends _ _
    | with_reducible exact deref_appends _
    | with_reducible exact queued_appends _ _
    | with_reducible exact noKey_appends _ _ _ _
    | with_reducible exact lifted _
    | with_reducible exact StateAppends.pure _
    | with_reducible apply append_mapM
    | with_reducible apply stateAppends_forIn
    | with_reducible apply StateAppends.bind
    | with_reducible apply append_ite
    | (maintenance_intro; try dsimp only)
    | split

theorem peerTailFinishPrefix_appends (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) : StateAppends (peerTailFinishPrefix attrs peer pid ret) := by
  have lifted {α : Type} (a : WG.M α) : StateAppends (liftWGPrefix a : MixedM α) := StateAppends.lift a
  have read (id : PeerId) : StateAppends (getPeerMixed id) := StateAppends.focus _ _ _
  have write (id : PeerId) (p : Peer) : StateAppends (setPeerMixed id p) := StateAppends.focus _ _ _
  have acquire (id : PeerId) : StateAppends (peerGetMixed id) := StateAppends.focus _ _ _
  have put (id : Option PeerId) : StateAppends (peerPutMixed id) := StateAppends.focus _ _ _
  unfold peerTailFinishPrefix configureKeepalivePrefix configureKeepaliveValuePrefix peerConfigOutPrefix
  repeat' first
    | with_reducible exact staged_appends _
    | with_reducible exact keepalive_appends _
    | with_reducible exact read _
    | with_reducible exact write _ _
    | with_reducible exact acquire _
    | with_reducible exact put _
    | with_reducible exact readKey_appends _
    | with_reducible exact writeKey_appends _ _
    | with_reducible exact readPacket_appends _
    | with_reducible exact writePacket_appends _ _
    | with_reducible exact newPacket_appends _
    | with_reducible exact erasePacket_appends _
    | with_reducible exact keyPut_appends _ _
    | with_reducible exact deref_appends _
    | with_reducible exact queued_appends _ _
    | with_reducible exact noKey_appends _ _ _ _
    | with_reducible exact lifted _
    | with_reducible exact StateAppends.pure _
    | with_reducible apply append_mapM
    | with_reducible apply stateAppends_forIn
    | with_reducible apply StateAppends.bind
    | with_reducible apply append_ite
    | (maintenance_intro; try dsimp only)
    | split

theorem peerTailFinishPrefix_erases (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    ErasesStatePrefix (peerTailFinishPrefix attrs peer pid ret) (peerTailFinishSource attrs peer pid ret) := by
  unfold peerTailFinishPrefix peerTailFinishSource configureKeepalivePrefix configureKeepaliveValuePrefix peerConfigOutPrefix
  simp only [bind_assoc, pure_bind]
  repeat' first
    | with_reducible exact peerPutMixed_erases _
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact setPeerMixed_erases _ _
    | with_reducible exact sendKeepalivePrefix_erases _
    | with_reducible exact sendStagedPacketsPrefix_erases _
    | exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | simp only [pure_bind]
    | with_reducible apply erasesStatePrefix_bind
    | (maintenance_intro; try dsimp only)
    | split

/-- The entire finish is one actual lifetime action. Its routing interpretation
is a lift of that same source, while its RX interpretation keeps all accesses. -/
def peerTailFinish (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    WGPrefix Event Int := access (peerTailFinishPrefix attrs peer pid ret)

theorem peerTailFinish_routing (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    StateProjectsPrefix routingEvent id (peerTailFinish attrs peer pid ret)
      (liftWGPrefix (peerTailFinishSource attrs peer pid ret)) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_erases_frame)
    routingEvent (access_erases (peerTailFinishPrefix_erases attrs peer pid ret))
      (access_routing _)

def peerConfigTail (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) : WGPrefix Event Int :=
  peerAllowedIps attrs peer pid (peerTailFinish attrs peer pid)

theorem peerConfigTail_routing (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    StateProjectsPrefix routingEvent id (peerConfigTail attrs peer pid)
      (peerConfigTailObserved attrs peer pid) :=
  peerAllowedIps_routing attrs peer pid _ _ (peerTailFinish_routing attrs peer pid)

theorem peerConfigTail_rx (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    StateProjectsPrefix rxEvent id (peerConfigTail attrs peer pid)
      (nativeRx (peerConfigTailPrefix attrs peer pid)) := by
  rw [peerConfigTailPrefix_factor]
  exact peerAllowedIps_rx_existing attrs peer pid _ _
    (peerTailFinishPrefix_appends attrs peer pid) (fun ret => access_rx _)

theorem peerConfigTail_rx_product (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    ProjectsPrefix rxEvent id (liftWGObserver (peerConfigTail attrs peer pid))
      (RxHistory.mixed (liftWGObserver (peerConfigTailPrefix attrs peer pid))) := by
  rw [← nativeRx_product]
  exact (peerConfigTail_rx attrs peer pid).liftWGObserver _ _

theorem peerConfigTailPrefix_appends (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    StateAppends (peerConfigTailPrefix attrs peer pid) := by
  have allowed (ip : AllowedIpAttrs) : StateAppends (setAllowedipPrefix pid ip) :=
    (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.allowed_appends) pid ip
  have out (ret : Int) : StateAppends (peerConfigOutPrefix attrs peer ret) :=
    (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.out_appends) attrs peer ret
  have lifted {α : Type} (a : WG.M α) : StateAppends (liftWGPrefix a : MixedM α) := StateAppends.lift a
  rw [peerConfigTailPrefix_factor]
  unfold peerAllowedIpsPrefix peerAllowedIpsWith
  repeat' first
    | with_reducible exact peerTailFinishPrefix_appends _ _ _ _
    | with_reducible exact allowed _
    | with_reducible exact out _
    | with_reducible exact lifted _
    | with_reducible exact StateAppends.pure _
    | with_reducible apply stateAppends_forIn
    | with_reducible apply StateAppends.bind
    | with_reducible apply append_ite
    | (maintenance_intro; try dsimp only)
    | split

end Leanux.Proofs.WG.Queues.RoutingJoint
