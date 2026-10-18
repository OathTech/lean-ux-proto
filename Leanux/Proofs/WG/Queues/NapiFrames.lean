import Leanux.Proofs.WG.Queues.RxPollStable
import Leanux.Proofs.WG.Origins.OwnerCompletion
import Leanux.Proofs.WG.Packets.PublicationPoll

/-! A narrow normal-return frame for the NAPI bit of surviving peers.
Deletion remains allowed; saved peer writes retain the bit read by the actual
source getter. No credit, residency, or successful-return premise is added. -/
namespace Leanux.Proofs.WG.Queues.NapiFrames
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do Lifetimes
open RxCredits

def napiView (w : WGWorld) : PeerId → Option Bool :=
  fun pid => (w.dev.bind fun d => d.peers[pid]?).map (·.napiScheduled)

def Retained (before : PeerId → Option Bool) (w : WGWorld) : Prop :=
  ∀ pid bit, napiView w pid = some bit → before pid = some bit

theorem refl (w : WGWorld) : Retained (napiView w) w := fun _ _ h => h

theorem trans (h : Retained initial w) (g : Retained (napiView w) v) : Retained initial v :=
  fun pid bit hv => h pid bit (g pid bit hv)

private theorem exact_view {α : Type} {a : WG.M α}
    (ha : SameView napiView a) (initial) : Preserves (Retained initial) a := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hi hr
  have hv := (ProjectedAction.iff_run_ambient _ _ _).mp ha w ambient result v ambient' hr
  simpa only [Retained,hv] using hi

private theorem stable {α : Type} {a : WG.M α}
    (ha : SameView stableView a) (initial) : Preserves (Retained initial) a :=
  exact_view (ha.of_factor (fun s pid => (s.2.2 pid).map Prod.snd) _
    (fun _ => by funext pid; simp only [NapiFrames.napiView,stableView,Option.map_map,Function.comp_def])) initial

private theorem store {α : Type} {a : WG.M α}
    (ha : SameWGStore a) (initial) : Preserves (Retained initial) a :=
  stable (stableView_kernel (project := id) ha) initial

theorem read_bind (initial) {α : Type} (pid : PeerId) (f : Peer → WG.M α)
    (hf : ∀ p, initial pid = some p.napiScheduled → Preserves (Retained initial) (f p)) :
    Preserves (Retained initial) (getPeer pid >>= f) := by
  apply hoare_bind _ _ (show Hoare (getPeer pid) (Retained initial)
    (fun p w => Retained initial w ∧ initial pid = some p.napiScheduled) from ?_)
  · intro p
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b hi hr
    exact (hoare_iff_run_ambient _ _ _).mp (hf p hi.2) w a result v b hi.1 hr
  · apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a p v b hi hr
    obtain ⟨rfl,_,d,hd,hp⟩ := getPeer_normal pid w v p a b hr
    exact ⟨hi,hi pid p.napiScheduled (by simp only [NapiFrames.napiView,hd,Option.bind_some,hp,Option.map_some])⟩

theorem set_saved (initial) (pid : PeerId) (p : Peer)
    (hp : initial pid = some p.napiScheduled) : Preserves (Retained initial) (setPeer pid p) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi hr
  cases hr
  intro q bit hq
  cases hd : w.dev with
  | none => simp [NapiFrames.napiView,hd] at hq
  | some d =>
    simp only [NapiFrames.napiView,hd,Option.map_some,Option.bind_some,Std.TreeMap.getElem?_insert,
      Std.LawfulEqOrd.compare_eq_iff_eq] at hq
    by_cases eq : pid = q
    · subst q
      simp only [ite_true,Option.map_some,Option.some.injEq] at hq
      exact hq ▸ hp
    · simp only [ite_eq_right eq] at hq
      exact hi q bit (by simpa only [NapiFrames.napiView,hd,Option.bind_some] using hq)

private theorem modifyDevice (f : Device → Device) (h : ∀ d, (f d).peers = d.peers) (initial) :
    Preserves (Retained initial) (modifyDev f) := by
  apply exact_view
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b hr
  cases hr
  funext pid
  change ((w.dev.map f).bind fun d => d.peers[pid]?).map (·.napiScheduled) = _
  simp only [Option.bind_map,Function.comp_def,h]
  rfl

theorem peerPut_preserves (pid : Option PeerId) (initial) :
    Preserves (Retained initial) (peerPut pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi hr
  cases result
  cases pid with
  | none =>
    simp [peerPut,branch,AmbientM.branch] at hr
    rcases hr with ⟨rfl,rfl⟩
    exact hi
  | some pid =>
    obtain ⟨d,p,hd,hp⟩ : ∃d p,w.dev=some d ∧ d.peers[pid]?=some p := by
      cases hd:w.dev with
      | none =>
        simp [peerPut,branch,AmbientM.branch,requireNotPending,getPeer,getDev,hd,
          invariant,AmbientM.invariant] at hr
        cases hr
      | some d =>
        cases hp:d.peers[pid]? with
        | none =>
          simp [peerPut,branch,AmbientM.branch,requireNotPending,getPeer,getDev,hd,hp,
            invariant,AmbientM.invariant] at hr
          cases hr
        | some p => exact ⟨d,p,rfl,hp⟩
    have effect := stable_payment_effect hd hp a b hr
    have bits : napiView v = napiView (paymentState w d pid p) := by
      funext q
      change ((v.dev.bind fun d => d.peers[q]?).map Peer.napiScheduled) =
        (((paymentState w d pid p).dev.bind fun d => d.peers[q]?).map Peer.napiScheduled)
      have h := congrArg (fun s => (s.2.2 q).map Prod.snd) effect
      simpa only [stableView,Option.map_map,Function.comp_def] using h
    intro q bit hq
    rw [bits] at hq
    by_cases final : p.refcount=1
    · simp only [paymentState,final,ite_true,NapiFrames.napiView,Option.bind_some,
        Std.TreeMap.getElem?_erase,Std.LawfulEqOrd.compare_eq_iff_eq] at hq
      by_cases eq : pid=q
      · simp [eq] at hq
      · simp only [ite_eq_right eq] at hq
        exact hi q bit (by simpa only [NapiFrames.napiView,hd,Option.bind_some] using hq)
    · simp only [paymentState,final,ite_false,NapiFrames.napiView,Option.bind_some,
        Std.TreeMap.getElem?_insert,Std.LawfulEqOrd.compare_eq_iff_eq] at hq
      by_cases eq : pid=q
      · subst q
        simp only [ite_true,Option.map_some,Option.some.injEq] at hq
        exact hi pid bit (by simp only [NapiFrames.napiView,hd,Option.bind_some,hp,Option.map_some,hq])
      · simp only [ite_eq_right eq] at hq
        exact hi q bit (by simpa only [NapiFrames.napiView,hd,Option.bind_some] using hq)

private theorem timer_bit (p : Peer) (t : PeerTimer) (v : Option UInt64) :
    (p.setTimer t v).napiScheduled = p.napiScheduled := by cases t <;> rfl

private theorem wheel_bit (p : Peer) (t : PeerTimer) (v : Option WheelEntry) :
    (p.setWheel t v).napiScheduled = p.napiScheduled := by cases t <;> rfl

macro "napi_step " initial:term : tactic => `(tactic| first
  | (env_bind_head getPeer; apply read_bind $initial; intro p hp)
  | (rx_retention_head setPeer; apply set_saved $initial; first | assumption | (simp only [timer_bit,wheel_bit]; assumption))
  | (rx_retention_head peerPut; exact peerPut_preserves _ $initial)
  | (rx_retention_head getPeer
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a p v b hi hr
     simpa only [(getPeer_normal _ w v p a b hr).1] using hi)
  | (rx_retention_head getDev; exact store getDev_sameWGStore $initial)
  | (rx_retention_head getKeypair
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a k v b hi hr
     simpa only [(KeyTimes.getKeypair_return _ w v k a b hr).1] using hi)
  | (rx_retention_head setKeypair; unfold setKeypair)
  | (rx_retention_head keypairGet; exact stable (stable_keypairGet _) $initial)
  | (rx_retention_head keypairPut; exact stable (stable_keypairPut _ _) $initial)
  | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp (Retained $initial))
  | (rx_retention_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ _)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (rx_retention_head get; exact hoare_consequence (hoare_get _)
      (fun _ h => h) (fun _ _ h => h.2))
  | (rx_retention_head modifyDev; apply modifyDevice; intro d; rfl)
  | (rx_retention_head modify; apply hoare_modify; intro w h; exact h)
  | (rx_retention_head ForIn.forIn
     apply list_view_spec id (Retained $initial)
     intro x b
     change Preserves (Retained $initial) _)
  | (rx_retention_head Functor.discard
     apply discard_view_spec id (Retained $initial)
     change Preserves (Retained $initial) _)
  | (first | rx_retention_head throw | rx_retention_head MonadExceptOf.throw
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a result v b hi hr
     cases hr)
  | rx_retention_step)

private theorem peerGet_preserves (pid : PeerId) (initial) :
    Preserves (Retained initial) (peerGet pid) := by
  unfold peerGet
  simp (config := {zeta := false}) only [requireNotPending,pure_bind,refcountInc,branch,branchCmp,unsupported]
  repeat' napi_step initial

macro "napi_traffic " initial:term : tactic => `(tactic| first
  | (rx_retention_head peerGet; exact peerGet_preserves _ $initial)
  | napi_step $initial)

macro "napi_skb" : tactic => `(tactic| first
  | (rx_retention_head getTxSkb; unfold getTxSkb)
  | (rx_retention_head setTxSkb; unfold setTxSkb)
  | (rx_retention_head newTxSkb; unfold newTxSkb)
  | (rx_retention_head freeTxSkb; unfold freeTxSkb)
  | (rx_retention_head liftSkb
     apply hoare_liftSkb
     intro w d store hi hd
     simpa only [Retained,NapiFrames.napiView,hd,Option.bind_some] using hi))

private theorem place_preserves (pid : PeerId) (t : PeerTimer) (expires clk : UInt64)
    (unit : Option Nat) (initial) : Preserves (Retained initial) (placeOnWheel pid t expires clk unit) := by
  unfold placeOnWheel
  simp (config := {zeta := false}) only [hidden,peekHiddenSite,invariant]
  repeat' napi_traffic initial

private theorem arm_preserves (pid : PeerId) (timer : PeerTimer) (delay : Nat)
    (jc : Option UInt64) (initial) : Preserves (Retained initial) (armTimer pid timer delay jc) := by
  unfold armTimer
  simp (config := {zeta := false}) only [getAmbient,hidden,invariant,unsupported]
  repeat' first
    | rxstack_preserves_join
    | (rx_retention_head placeOnWheel; exact place_preserves _ _ _ _ _ initial)
    | napi_traffic initial

private theorem del_preserves (pid : PeerId) (timer : PeerTimer) (initial) :
    Preserves (Retained initial) (delTimer pid timer) := by
  unfold delTimer
  repeat' napi_traffic initial

private theorem mod_preserves (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) (initial) :
    Preserves (Retained initial) (modPeerTimer site pid timer delay) := by
  unfold modPeerTimer modPeerTimerGuard WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head callerJiffies; exact (callerJiffies_sameWGWorld _).wp (Retained initial))
    | (rx_retention_head armTimer; exact arm_preserves _ _ _ _ initial)
    | napi_traffic initial

private theorem sendQueued_preserves (pid : PeerId) (retry : Bool) (initial) :
    Preserves (Retained initial) (sendQueuedHandshakeInitiation pid retry) := by
  unfold sendQueuedHandshakeInitiation
  simp (config := {zeta := false}) only [branch,peekQueuedUnit,recordQueued]
  repeat' napi_traffic initial

private theorem received_preserves (pid : PeerId) (kid : KeypairId) (initial) :
    Preserves (Retained initial) (receivedWithKeypair pid kid) := by
  unfold receivedWithKeypair
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  simp (config := {zeta := false}) only [branch]
  repeat' napi_traffic initial

private theorem fresh_preserves (pid : PeerId) (initial) :
    Preserves (Retained initial) (keepKeyFreshRx pid) := by
  unfold keepKeyFreshRx WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head sendQueuedHandshakeInitiation; exact sendQueued_preserves _ _ initial)
    | napi_traffic initial

private theorem choose_preserves (pid : PeerId) (initial) :
    Preserves (Retained initial) (cpumaskChooseOnline pid) := by
  unfold cpumaskChooseOnline
  simp (config := {zeta := false}) only [branch,Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' napi_traffic initial

private theorem enqueueDevice_preserves (pid : PeerId) (item : List SkbId) (initial) :
    Preserves (Retained initial) (enqueuePerDeviceAndPeer pid item) := by
  unfold enqueuePerDeviceAndPeer
  simp (config := {zeta := false}) only [branch,queueDeviceWork,invariant]
  repeat' first
    | (rx_retention_head cpumaskNextOnlineFrom; exact store (cpumaskNextOnlineFrom_sameStore _) initial)
    | napi_skb
    | napi_traffic initial

private theorem enqueuePeer_preserves (item : List SkbId) (state : PacketState) (initial) :
    Preserves (Retained initial) (enqueuePerPeerTx item state) := by
  unfold enqueuePerPeerTx
  simp (config := {zeta := false}) only [peekQueuedUnit,recordQueued,invariant]
  repeat' first
    | (rx_retention_head cpumaskChooseOnline; exact choose_preserves _ initial)
    | napi_skb
    | napi_traffic initial

private theorem create_preserves (pid : PeerId) (item : List SkbId) (initial) :
    Preserves (Retained initial) (createData pid item) := by
  unfold createData
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head enqueuePerDeviceAndPeer; exact enqueueDevice_preserves _ _ initial)
    | (rx_retention_head enqueuePerPeerTx; exact enqueuePeer_preserves _ _ initial)
    | napi_skb
    | napi_traffic initial

private theorem noKey_preserves (pid : PeerId) (packets : List Leanux.WG.Packet)
    (keypair : Option KeypairId) (invalid : Bool) (initial) :
    Preserves (Retained initial) (stagedOutNokey pid packets keypair invalid) := by
  unfold stagedOutNokey
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head sendQueuedHandshakeInitiation; exact sendQueued_preserves _ _ initial)
    | napi_traffic initial

private theorem submit_preserves (pid kid : Nat) (packets : List DataPacket) (initial) :
    Preserves (Retained initial) (stagedSubmit pid kid packets) := by
  unfold stagedSubmit Affiliation.sendAcquire
  repeat' first
    | (rx_retention_head createData; exact create_preserves _ _ initial)
    | (rx_retention_head List.mapM
       apply mapM_view_spec id (Retained initial)
       intro packet
       change Preserves (Retained initial) _)
    | napi_skb
    | napi_traffic initial

private theorem stagedKey_preserves (pid kid : Nat) (packets : List Leanux.WG.Packet) (initial) :
    Preserves (Retained initial) (stagedKeySource pid kid packets) := by
  unfold stagedKeySource
  simp (config := {zeta := false}) only [branch,branchCmp]
  repeat' first
    | (rx_retention_head stagedOutNokey; exact noKey_preserves _ _ _ _ initial)
    | (rx_retention_head stagedSubmit; exact submit_preserves _ _ _ initial)
    | (rx_retention_head ipTunnelEcnEncap; exact (ipTunnelEcnEncap_sameWGWorld _).wp (Retained initial))
    | napi_traffic initial

theorem staged_preserves (pid : PeerId) (initial) :
    Preserves (Retained initial) (sendStagedPackets pid) := by
  rw [← stagedFullSource_eq]
  unfold stagedFullSource
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head stagedOutNokey; exact noKey_preserves _ _ _ _ initial)
    | (rx_retention_head stagedKeySource; exact stagedKey_preserves _ _ _ initial)
    | napi_traffic initial

private theorem endpoint_preserves (pid : PeerId) (e : Endpoint) (initial) :
    Preserves (Retained initial) (setPeerEndpoint pid e) := by
  unfold setPeerEndpoint dstCacheReset requireNotPending
  simp (config := {zeta := false}) only [branch,getAmbient,hiddenJiffies]
  repeat' first
    | (rx_retention_head endpointEq; exact store (endpointEq_sameStore _ _) initial)
    | napi_traffic initial

private theorem lookup_preserves (root : Option NodeId) (bits key : Nat) (initial) :
    Preserves (Retained initial) (lookup root bits key) := by
  have aip {α : Type} (a : AipM α) : Preserves (Retained initial) (monadLift a : WG.M α) := by
    apply hoare_liftAip
    intro w d s hi hd
    simpa only [Retained,napiView,hd,Option.bind_some] using hi
  unfold lookup swapEndian
  simp (config := {zeta := false}) only [branch,unsupported,invariant]
  repeat' first
    | (rx_retention_head peerGetMaybeZero; exact stable (stable_peerGetMaybeZero _) initial)
    | (allocation_release_lift_from AipM; exact aip _)
    | napi_traffic initial

private theorem lookupSrc_preserves (protocol : Nat) (bytes : List UInt8) (initial) :
    Preserves (Retained initial) (lookupSrc protocol bytes) := by
  unfold lookupSrc
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head lookup; exact lookup_preserves _ _ _ initial)
    | napi_traffic initial

private theorem handshake_preserves (pid : PeerId) (site : HiddenSite) (initial) :
    Preserves (Retained initial) (timersHandshakeComplete pid site) := by
  unfold timersHandshakeComplete
  simp (config := {zeta := false}) only [hidden]
  repeat' first
    | (rx_retention_head delTimer; exact del_preserves _ _ initial)
    | napi_traffic initial

private theorem traversal_preserves (pid : PeerId) (initial) :
    Preserves (Retained initial) (timersTraversal pid) := by
  unfold timersTraversal
  simp (config := {zeta := false}) only [branchCmp]
  repeat' first
    | (rx_retention_head modPeerTimer; exact mod_preserves _ _ _ _ initial)
    | napi_traffic initial

private theorem dataReceived_preserves (pid : PeerId) (initial) :
    Preserves (Retained initial) (timersDataReceived pid) := by
  unfold timersDataReceived
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head modPeerTimer; exact mod_preserves _ _ _ _ initial)
    | napi_traffic initial

private theorem stats_preserves (pid : PeerId) (len : Nat) (initial) :
    Preserves (Retained initial) (updateRxStats pid len) := by
  unfold updateRxStats
  repeat' napi_traffic initial

private theorem dishonest_preserves (why : Dishonest) (initial) :
    Preserves (Retained initial) (dishonest why) := by
  cases why <;> unfold dishonest <;> apply modifyDevice <;> intro d <;> rfl

/-- The complete native call retains every surviving NAPI bit, including
staged sending and the source lookup's peer payment. -/
theorem consumeDataDone_preserves (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) (initial) :
    Preserves (Retained initial) (consumeDataDone pid pkt endpoint) := by
  unfold consumeDataDone WG.andM WG.orM timersAnyAuthenticatedPacketReceived
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head setPeerEndpoint; exact endpoint_preserves _ _ initial)
    | (rx_retention_head receivedWithKeypair; exact received_preserves _ _ initial)
    | (rx_retention_head sendStagedPackets; exact staged_preserves _ initial)
    | (rx_retention_head keepKeyFreshRx; exact fresh_preserves _ initial)
    | (rx_retention_head timersHandshakeComplete; exact handshake_preserves _ _ initial)
    | (rx_retention_head timersTraversal; exact traversal_preserves _ initial)
    | (rx_retention_head timersDataReceived; exact dataReceived_preserves _ initial)
    | (rx_retention_head delTimer; exact del_preserves _ _ initial)
    | (rx_retention_head updateRxStats; exact stats_preserves _ _ initial)
    | (rx_retention_head dishonest; exact dishonest_preserves _ initial)
    | (rx_retention_head lookupSrc; exact lookupSrc_preserves _ _ initial)
    | (rx_retention_head inetEcnDecapsulate; exact store (inetEcnDecapsulate_sameWGStore _ _ _) initial)
    | napi_traffic initial

private theorem lookupDst_preserves (family addr : Nat) (initial) :
    Preserves (Retained initial) (lookupDst family addr) := by
  unfold lookupDst
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head lookup; exact lookup_preserves _ _ _ initial)
    | napi_traffic initial

private theorem trim_preserves (pid : PeerId) (initial) :
    Preserves (Retained initial) (xmitTrim pid) := by
  unfold xmitTrim
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',branch]
  repeat' napi_traffic initial

private theorem splice_preserves (pid : PeerId) (packets : List WG.Packet) (initial) :
    Preserves (Retained initial) (xmitSplice pid packets) := by
  unfold xmitSplice
  repeat' napi_traffic initial

/-- Every normal transmit return, including negative status, retains the NAPI
bit of surviving peers. Loopback's actual pending-NAPI guard is retained. -/
theorem wgXmit_preserves (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) (initial) :
    Preserves (Retained initial) (wgXmit family addr packets mtu) := by
  rw [wgXmitSource_eq]
  unfold wgXmitSource WG.andM
  simp (config := {zeta := false}) only [branch,invariant,skipCutSites,envOk]
  repeat' first
    | (rx_retention_head lookupDst; exact lookupDst_preserves _ _ initial)
    | (rx_retention_head xmitTrim; exact trim_preserves _ initial)
    | (rx_retention_head xmitSplice; exact splice_preserves _ _ initial)
    | (rx_retention_head sendStagedPackets; exact staged_preserves _ initial)
    | (rx_retention_head loopbackSend; exact store (loopbackSend_kernel _ _) initial)
    | (allocation_release_lift_from Net.M; exact hoare_liftRouting _ _ (fun _ _ hi => hi))
    | napi_traffic initial

private theorem product_store {α : Type} {a : Leanux.M α} (frame : SameProductStore a) (initial) :
    Preserves (fun w : World => Retained initial w.wg) a := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi hr
  have fields := (ProjectedAction.iff_run _ _ _).mp frame w result v hr
  have dev : v.wg.dev = w.wg.dev := congrArg (fun s : ProductStore43 => s.2.2.2.dev) fields
  simpa only [Retained,napiView,dev] using hi

private theorem reply4_preserves (dst : Nat) (bytes : List UInt8) (initial) :
    Preserves (fun w : World => Retained initial w.wg) (Leanux.Env.Stack.reply4 dst bytes) := by
  let P := fun w : World => Retained initial w.wg
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have routing {α : Type} (a : Net.M α) : Preserves P (monadLift a : Leanux.M α) :=
    PublicationPoll.native_product _ _ (store (liftRouting_sameWGStore a) initial)
  have dev : Preserves P (monadLift getDev : Leanux.M Device) :=
    PublicationPoll.native_product _ _ (store getDev_sameWGStore initial)
  have send (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
      Preserves P (monadLift (wgXmit family addr packets mtu) : Leanux.M Int) :=
    PublicationPoll.native_product _ _ (wgXmit_preserves family addr packets mtu initial)
  have discarded {α : Type} (a : Leanux.M α) (ha : Preserves P a) : Preserves P (discard a) :=
    discard_view_spec id P a ha
  rxstack_preserves_source [Leanux.Env.Stack.reply4,skipCut,unsupported]
    using [dev,send,ambient,routing,discarded]

private theorem receive4_preserves (bytes : List UInt8) (initial) :
    Preserves (fun w : World => Retained initial w.wg) (Leanux.Env.Stack.receive4 bytes) := by
  let P := fun w : World => Retained initial w.wg
  have stopped (a : Leanux.M Unit) (hs : ∀ w, ∃ e, a.run w = .error e)
      (next : Unit → Leanux.M Unit) : Preserves P (a >>= next) :=
    (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentStack.«0».Leanux.Proofs.WG.CurrentStack.stopped_bind) a hs next P
  have excluded := fun row tail => stopped (Leanux.Env.Stack.excluded row)
    (stackExcluded_failure row) tail
  have invalid := fun why tail => stopped (Leanux.invariant why) (fun _ => ⟨_,rfl⟩) tail
  have unsupported := fun why tail => stopped (Leanux.unsupported why) (fun _ => ⟨_,rfl⟩) tail
  have excludedAlone (row : String) : Preserves P (Leanux.Env.Stack.excluded row) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w x v hi hr
    obtain ⟨e,he⟩ := stackExcluded_failure row w
    rw [he] at hr
    contradiction
  have route (src dst : Nat) : Preserves P
      (monadLift (monadLift (Net.routeInput4 src dst) : WG.M _) : Leanux.M _) :=
    PublicationPoll.native_product _ _ (store (liftRouting_sameWGStore _) initial)
  have read : Preserves P (getWG : Leanux.M WGWorld) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w x v hi hr
    cases hr
    exact hi
  have write (f : EnvWorld → EnvWorld) : Preserves P (modifyEnv f) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w x v hi hr
    cases hr
    exact hi
  unfold Leanux.Env.Stack.receive4
  repeat' first
    | (env_bind_head Leanux.Env.Stack.excluded; exact excluded _ _)
    | (env_bind_head Leanux.invariant; exact invalid _ _)
    | (env_bind_head Leanux.unsupported; exact unsupported _ _)
    | (allocation_release_head Leanux.Env.Stack.excluded; exact excludedAlone _)
    | (allocation_release_head Leanux.Env.Stack.reply4; exact reply4_preserves _ _ initial)
    | (allocation_release_head MonadLift.monadLift; exact route _ _)
    | (allocation_release_head liftM; exact route _ _)
    | (allocation_release_head getWG; exact read)
    | (allocation_release_head modifyEnv; exact write _)
    | rx_retention_step
    | env_ordinary_head_reduce
    | env_ordinary_head_match

theorem deliverInner_preserves (bytes : List UInt8) (initial) :
    Preserves (fun w : World => Retained initial w.wg) (Leanux.Env.deliverInner bytes) := by
  have h4 := receive4_preserves bytes initial
  have h6 := product_store (stackReceive6_sameKernel bytes) initial
  have ambient {α : Type} (a : AmbientM α) :
      Preserves (fun w : World => Retained initial w.wg) (monadLift a : Leanux.M α) :=
    productAmbient_spec a _ (fun _ _ hi => hi)
  rxstack_preserves_source [Leanux.Env.deliverInner,Leanux.Env.Stack.receive,invariant]
    using [h4,h6,ambient]

/-- The concrete product-domain Stack callback used by the actual receive
poll. Only surviving peers are constrained; every source Stop remains allowed. -/
theorem stack_preserves (packets : List (List UInt8)) (initial) :
    Preserves (fun w : World => Retained initial w.wg) (packets.forM Leanux.Env.deliverInner) := by
  induction packets with
  | nil => exact preserves_pure _
  | cons bytes rest ih =>
    simp only [List.forM_eq_forM,List.forM_cons]
    exact preserves_bind (deliverInner_preserves bytes initial) (fun _ => ih)

end Leanux.Proofs.WG.Queues.NapiFrames
