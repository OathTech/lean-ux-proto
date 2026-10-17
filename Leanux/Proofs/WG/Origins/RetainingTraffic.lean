import Leanux.Proofs.WG.Origins.RetainingLeaves
import Leanux.Proofs.WG.Queues.RxBorrow
import Leanux.Proofs.WG.Queues.RxTxFrames
import Leanux.Proofs.WG.Queues.TxDispositionEndpoints
import Leanux.Proofs.WG.Queues.TxRingWorker
import Leanux.Proofs.WG.Queues.RxPollPrefix
import Leanux.Proofs.WG.Queues.RxRingWorker
import Leanux.Proofs.Framing.Batch
import Leanux.Proofs.WG.Lifetimes.BatchNapi
import Leanux.Proofs.Framing.WGData
import Leanux.Proofs.Framing.WGReceiveHeaders

/-! Original non-installing packet paths retain every surviving valid receiving
material and its nullable owner. Callback contracts are explicit until discharged
by the actual stack; neither residence nor packet authorization is asserted. -/
namespace Leanux.Proofs.WG.Origins.Retaining
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Leanux.Proofs.WG.Lifetimes Leanux.Proofs.WG.Queues Std.Do
set_option pp.structureInstances false

open Lean Meta Elab Tactic

/-- The original unrestricted product contracts remain available beside the
native calls. This is an observation of the actual World, not an execution layer. -/
abbrev ProductRetainsCall (a : Leanux.M α) := ProjectedRetainsCall World.wg a

theorem RetainsCall.product {a : WG.M α} (ha : RetainsCall a) :
    ProductRetainsCall (liftWG a) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w x v hr
  rw [liftWG_run] at hr
  cases he : (a.run w.wg).run w.ambient with
  | error e => simp [he,Except.map] at hr
  | ok out =>
    rcases out with ⟨⟨y,g⟩,ambient⟩
    simp [he,Except.map] at hr
    rcases hr with ⟨rfl,rfl⟩
    exact (ProjectedAction.iff_run_ambient _ _ _).mp ha _ _ _ _ _ he

macro "traffic_skb " P:term : tactic => `(tactic|
  first
    | (index_material_head getTxSkb; unfold getTxSkb)
    | (index_material_head setTxSkb; unfold setTxSkb)
    | (index_material_head newTxSkb; unfold newTxSkb)
    | (index_material_head freeTxSkb; unfold freeTxSkb)
    | (index_material_head getRxSkb; unfold getRxSkb)
    | (index_material_head setRxSkb; unfold setRxSkb)
    | (index_material_head newRxSkb; unfold newRxSkb)
    | (index_material_head freeRxSkb; unfold freeRxSkb)
    | (index_material_head liftSkb
       apply hoare_liftSkb _ (fun w => $P (view w))
       intro w d store hw hd
       simpa only [view,hd,Option.map_some] using hw))

macro "traffic_basic " P:term : tactic => `(tactic|
  first
    | (first | index_material_head monadLift | index_material_head MonadLift.monadLift | index_material_head MonadLiftT.monadLift
       simp only [monadLift_self])
    | traffic_skb $P
    | (index_material_head WG.orM; unfold WG.orM)
    | (index_material_head WG.andM; unfold WG.andM)
    | (run_tac do
         let t ← getMainTarget
         let args := t.getAppArgs
         unless args.size ≥ 3 do throwError "not a contract"
         let head := args[args.size-3]!.getAppFn
         let .const n _ := head | throwError "not a peer modifier"
         unless n.toString.endsWith ".modifyPeer" do throwError "not a peer modifier"
       exact (modifyPeer_material _ _).wp $P)
    | (index_material_head peerGet; exact (peerGet_material _).wp $P)
    | (index_material_head peerPut; exact (peerPut_material _).wp $P)
    | material_known $P
    | material_basic $P)

macro "traffic_key " initial:term : tactic => `(tactic|
  first
    | (index_material_head keypairGet; exact (keypairGet_material _).wp $initial)
    | (index_material_head keypairPut; exact (keypairPut_material _ _).wp $initial))


theorem sendQueuedHandshakeInitiation_material (pid : PeerId) (retry : Bool) :
    RetainsCall (sendQueuedHandshakeInitiation pid retry) := by
  apply ProjectedAction.of_wp
  intro initial
  refine hoare_consequence
    (P := fun w => RetainsView initial (view w))
    (Q := fun _ w => RetainsView initial (view w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    dsimp only [id] at h
    rw [h]
    exact RetainsView.refl _
  unfold sendQueuedHandshakeInitiation
  material_lower
  try unfold recordQueued
  try unfold peekQueuedUnit
  try unfold queueDeviceWork
  repeat' traffic_basic (RetainsView initial)

theorem txDevice_material (u : TxDeviceUpdate) : SameView view (modifyDev u.apply) :=
  modifyDev_material _ (fun d => by cases u <;> rfl)

theorem cpumaskChooseOnline_material (pid : PeerId) : SameView view (cpumaskChooseOnline pid) := by
  intro initial
  unfold cpumaskChooseOnline
  simp only [Nat.mod_one, Std.Legacy.Range.forIn_eq_forIn_range']
  material_lower
  try unfold recordQueued
  try unfold peekQueuedUnit
  try unfold queueDeviceWork
  repeat' traffic_basic (fun t => t = initial)

theorem enqueuePerDeviceAndPeer_material (pid : PeerId) (item : List SkbId) :
    SameView view (enqueuePerDeviceAndPeer pid item) := by
  intro initial
  unfold enqueuePerDeviceAndPeer cpumaskNextOnlineFrom queueDeviceWork
  material_lower
  try unfold recordQueued
  try unfold peekQueuedUnit
  try unfold queueDeviceWork
  repeat' traffic_basic (fun t => t = initial)

theorem enqueuePerPeerTx_material (item : List SkbId) (state : PacketState) :
    RetainsCall (enqueuePerPeerTx item state) := by
  apply ProjectedAction.of_wp
  intro initial
  refine hoare_consequence
    (P := fun w => RetainsView initial (view w))
    (Q := fun _ w => RetainsView initial (view w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    dsimp only [id] at h
    rw [h]
    exact RetainsView.refl _
  unfold enqueuePerPeerTx
  material_lower
  try unfold recordQueued
  try unfold peekQueuedUnit
  try unfold queueDeviceWork
  repeat' first
    | (index_material_head cpumaskChooseOnline; exact (cpumaskChooseOnline_material _).wp (RetainsView initial))
    | traffic_basic (RetainsView initial)

theorem createData_material (pid : PeerId) (item : List SkbId) : RetainsCall (createData pid item) := by
  apply ProjectedAction.of_wp
  intro initial
  refine hoare_consequence
    (P := fun w => RetainsView initial (view w))
    (Q := fun _ w => RetainsView initial (view w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    dsimp only [id] at h
    rw [h]
    exact RetainsView.refl _
  unfold createData
  material_lower
  try unfold recordQueued
  try unfold peekQueuedUnit
  try unfold queueDeviceWork
  repeat' first
    | (index_material_head enqueuePerDeviceAndPeer; exact (enqueuePerDeviceAndPeer_material _ _).wp (RetainsView initial))
    | (index_material_head enqueuePerPeerTx; exact (enqueuePerPeerTx_material _ _).wp initial)
    | traffic_key initial
    | traffic_basic (RetainsView initial)


private theorem keyUpdateThen_material (initial : View) (id : KeypairId)
    (f : Keypair → Keypair)
    (valid : ∀ k, (f k).receiving.isValid = true → k.receiving.isValid = true)
    (keep : ∀ k, KeyLe (f k) k)
    (next : Keypair → WG.M α)
    (hn : ∀ k, Hoare (next k) (fun w => RetainsView initial (view w))
      (fun _ w => RetainsView initial (view w))) :
    Hoare (do let k ← getKeypair id; setKeypair id (f k); next k)
      (fun w => RetainsView initial (view w)) (fun _ w => RetainsView initial (view w)) := by
  apply hoare_bind (getKeypair id) _ (getKeypair_spec (RetainsView initial) id)
  intro k
  apply hoare_bind (setKeypair id (f k)) _
  · exact hoare_consequence
      (setKeypair_spec (RetainsView initial) (fun _ _ hr hi => hi.trans hr) id (f k))
      (fun _ h => ⟨h.1, fun hv => ⟨k,h.2,valid k hv,keep k⟩⟩) (fun _ _ h => h)
  · intro _
    exact hn k

elab "traffic_key_update" : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  let args := target.getAppArgs
  unless (target.isAppOf ``Hoare || target.isAppOf ``Triple) && args.size ≥ 3 do
    throwError "not an endpoint contract"
  let action := args[args.size-3]!.consumeMData
  unless action.isAppOf ``Bind.bind do throwError "not a bind"
  let aa := action.getAppArgs
  unless aa[aa.size-2]!.isAppOf ``getKeypair do throwError "not a key read"
  lambdaTelescope aa.back! fun _ body => do
    let rec head : Nat → Expr → Expr
      | 0, e => e
      | n+1, e => match e.consumeMData with
        | .letE _ _ v b _ => head n (b.instantiate1 v)
        | e => e.headBeta
    let body := head 16 body
    unless body.isAppOf ``Bind.bind do throwError "not an immediate update"
    let ba := body.getAppArgs
    unless ba[ba.size-2]!.isAppOf ``setKeypair do throwError "not a key write"
  evalTactic (← `(tactic| apply keyUpdateThen_material))
  evalTactic (← `(tactic| all_goals try (solve | intro k h; exact h)))
  evalTactic (← `(tactic| all_goals try (solve | intro k; exact ⟨rfl,Or.inr rfl⟩)))

theorem stagedOutNokey_material (pid : PeerId) (packets : List Packet)
    (keypair : Option KeypairId) (invalid : Bool) :
    RetainsCall (stagedOutNokey pid packets keypair invalid) := by
  apply ProjectedAction.of_wp
  intro initial
  refine hoare_consequence
    (P := fun w => RetainsView initial (view w))
    (Q := fun _ w => RetainsView initial (view w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    dsimp only [id] at h
    rw [h]
    exact RetainsView.refl _
  unfold stagedOutNokey
  material_lower
  repeat' first
    | traffic_key_update
    | (index_material_head sendQueuedHandshakeInitiation; exact (sendQueuedHandshakeInitiation_material _ _).wp initial)
    | traffic_key initial
    | traffic_basic (RetainsView initial)

elab "traffic_join" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  let args := target.getAppArgs
  unless (target.isAppOf ``Hoare || target.isAppOf ``Triple) && args.size ≥ 3 do
    throwError "not an endpoint contract"
  let i := args.size-3
  let .letE name ty value body nondep := args[i]!.consumeMData
    | throwError "not a local continuation"
  unless name.toString == "outNokey" || name.toString == "err" || name.toString == "reject" do
    throwError "not a source continuation"
  let renamed := Expr.letE `__do_jp_traffic ty value body nondep
  replaceMainGoal [← goal.replaceTargetDefEq (mkAppN target.getAppFn (args.set! i renamed))]
  evalTactic (← `(tactic| material_join))

theorem sendStagedPackets_material (pid : PeerId) : RetainsCall (sendStagedPackets pid) := by
  apply ProjectedAction.of_wp
  intro initial
  refine hoare_consequence
    (P := fun w => RetainsView initial (view w))
    (Q := fun _ w => RetainsView initial (view w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    dsimp only [id] at h
    rw [h]
    exact RetainsView.refl _
  unfold sendStagedPackets
  material_lower
  repeat' first
    | traffic_join
    | traffic_key_update
    | (index_material_head sendQueuedHandshakeInitiation; exact (sendQueuedHandshakeInitiation_material _ _).wp initial)
    | (index_material_head createData; exact (createData_material _ _).wp initial)
    | (index_material_head ipTunnelEcnEncap; exact ((ipTunnelEcnEncap_sameWGWorld _).factor view).wp (RetainsView initial))
    | (index_material_head List.mapM; apply mapM_view_spec view (RetainsView initial); intro pkt)
    | traffic_key initial
    | traffic_basic (RetainsView initial)

theorem sendKeepalive_material (pid : PeerId) : RetainsCall (sendKeepalive pid) := by
  apply ProjectedAction.of_wp
  intro initial
  refine hoare_consequence
    (P := fun w => RetainsView initial (view w))
    (Q := fun _ w => RetainsView initial (view w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    dsimp only [id] at h
    rw [h]
    exact RetainsView.refl _
  unfold sendKeepalive
  material_lower
  repeat' first
    | (index_material_head sendStagedPackets; exact (sendStagedPackets_material _).wp initial)
    | traffic_basic (RetainsView initial)

private theorem borrowed_material {w v : WGWorld}
    (hb : PeerBorrow.Borrowed (wgStoreView w) result (wgStoreView v)) :
    view v = view w := by
  change (wgStoreView v).dev.map (fun d => (d.ifindex, fun q => d.keypairs[q]?)) =
    (wgStoreView w).dev.map (fun d => (d.ifindex, fun q => d.keypairs[q]?))
  cases result with
  | none => change wgStoreView v = wgStoreView w at hb; rw [hb]
  | some pid =>
    obtain ⟨d,p,hd,_,_,hk⟩ := hb
    simp [hk,hd]

theorem lookup_material (root : Option NodeId) (bits key : Nat) :
    SameView view (lookup root bits key) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hr
  exact borrowed_material ((hoare_iff_run_ambient _ _ _).mp
    (RxBorrow.lookup_spec root bits key (wgStoreView w)) w ambient result v ambient' rfl hr)

theorem lookupSrc_material (protocol : Nat) (bytes : List UInt8) :
    SameView view (lookupSrc protocol bytes) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hr
  exact borrowed_material ((hoare_iff_run_ambient _ _ _).mp
    (RxBorrow.lookupSrc_spec protocol bytes (wgStoreView w)) w ambient result v ambient' rfl hr)

theorem lookupDst_material (family addr : Nat) : SameView view (lookupDst family addr) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hr
  exact borrowed_material ((hoare_iff_run_ambient _ _ _).mp
    (RxBorrow.lookupDst_spec family addr (wgStoreView w)) w ambient result v ambient' rfl hr)

theorem sendSkbToPeer_material (pid : PeerId) (bytes : List UInt8) (ds : Nat) :
    SameView view (sendSkbToPeer pid bytes ds) := by
  intro initial
  unfold sendSkbToPeer
  material_lower
  repeat' first
    | (index_material_head send4; exact (send4_material _ _ _ _ _).wp (fun t => t = initial))
    | (index_material_head send6; exact (send6_material _ _ _ _ _).wp (fun t => t = initial))
    | traffic_basic (fun t => t = initial)

theorem timersDataSent_material (pid : PeerId) : SameView view (timersDataSent pid) := by
  intro initial
  unfold timersDataSent
  material_lower
  repeat' first
    | (index_material_head modPeerTimerGuard; exact (modPeerTimerGuard_material _).wp (fun t => t = initial))
    | (index_material_head armTimer; exact (armTimer_material _ _ _ _).wp (fun t => t = initial))
    | traffic_basic (fun t => t = initial)

theorem keepKeyFresh_material (pid : PeerId) : RetainsCall (keepKeyFresh pid) := by
  apply ProjectedAction.of_wp
  intro initial
  refine hoare_consequence
    (P := fun w => RetainsView initial (view w))
    (Q := fun _ w => RetainsView initial (view w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    dsimp only [id] at h
    rw [h]
    exact RetainsView.refl _
  unfold keepKeyFresh WG.andM WG.orM
  material_lower
  repeat' first
    | (index_material_head sendQueuedHandshakeInitiation; exact (sendQueuedHandshakeInitiation_material _ _).wp initial)
    | traffic_basic (RetainsView initial)

theorem createDataDone_material (pid : PeerId) (item : List SkbId) :
    RetainsCall (createDataDone pid item) := by
  apply ProjectedAction.of_wp
  intro initial
  refine hoare_consequence
    (P := fun w => RetainsView initial (view w))
    (Q := fun _ w => RetainsView initial (view w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    dsimp only [id] at h
    rw [h]
    exact RetainsView.refl _
  unfold createDataDone WG.andM
  material_lower
  repeat' first
    | (index_material_head timersTraversal; exact (timersTraversal_material _).wp (RetainsView initial))
    | (index_material_head timersAnyAuthenticatedPacketSent; exact (timersAnyAuthenticatedPacketSent_material _).wp (RetainsView initial))
    | (index_material_head sendSkbToPeer; exact (sendSkbToPeer_material _ _ _).wp (RetainsView initial))
    | (index_material_head timersDataSent; exact (timersDataSent_material _).wp (RetainsView initial))
    | (index_material_head keepKeyFresh; exact (keepKeyFresh_material _).wp initial)
    | traffic_basic (RetainsView initial)

theorem txStep_material (pid : PeerId) : RetainsCall (txStep pid) := by
  apply ProjectedAction.of_wp
  intro initial
  refine hoare_consequence
    (P := fun w => RetainsView initial (view w))
    (Q := fun _ w => RetainsView initial (view w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    dsimp only [id] at h
    rw [h]
    exact RetainsView.refl _
  rw [← TxDisposition.stepSource_eq]
  unfold TxDisposition.stepSource TxDisposition.bodySource TxDisposition.disposeSource WG.andM
  material_lower
  repeat' first
    | (index_material_head PrevQueue.peek; exact (sameView_of_sameWG (project := id) (prevQueuePeek_sameWGStore _)).wp (RetainsView initial))
    | (index_material_head createDataDone; exact (createDataDone_material _ _).wp initial)
    | traffic_key initial
    | traffic_basic (RetainsView initial)

theorem workerIter_material (worker : Worker) (pid : Option Nat)
    (step afterItem : Leanux.M Bool)
    (hs : ProductRetainsCall step) (ha : ProductRetainsCall afterItem) :
    ProductRetainsCall (workerIter worker pid step afterItem) := by
  intro initial
  refine hoare_consequence (P := fun w => RetainsView initial (view w.wg))
    (Q := fun _ w => RetainsView initial (view w.wg)) ?_
    (fun w h => by change view w.wg = initial at h; rw [h]; exact RetainsView.refl _) (fun _ _ h => h)
  unfold workerIter
  apply preserves_bind (ProjectedRetainsCall.wp hs initial)
  intro did
  cases did with
  | false => exact preserves_pure _
  | true =>
    apply preserves_bind (ProjectedRetainsCall.wp ha initial)
    intro resched
    exact preserves_pure _

theorem txIter_material (pid : PeerId) (need : Leanux.M Bool)
    (hn : ProductRetainsCall need) : ProductRetainsCall (txIter pid need) := by
  apply workerIter_material _ _ _ _ (RetainsCall.product (txStep_material pid))
  intro initial
  refine hoare_consequence (P := fun w => RetainsView initial (view w.wg))
    (Q := fun _ w => RetainsView initial (view w.wg)) ?_
    (fun w h => by change view w.wg = initial at h; rw [h]; exact RetainsView.refl _) (fun _ _ h => h)
  apply preserves_bind (ProjectedRetainsCall.wp hn initial)
  intro resched
  exact productAmbient_spec (AmbientM.branch .txNeedResched resched) _ (fun _ _ hi => hi)

theorem xmitTrim_material (pid : PeerId) : SameView view (xmitTrim pid) := by
  intro initial
  unfold xmitTrim
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  material_lower
  repeat' traffic_basic (fun t => t = initial)

theorem xmitSplice_material (pid : PeerId) (packets : List Packet) :
    SameView view (xmitSplice pid packets) := by
  intro initial
  unfold xmitSplice
  material_lower
  repeat' traffic_basic (fun t => t = initial)

theorem wgXmit_material (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    RetainsCall (wgXmit family addr packets mtu) := by
  apply ProjectedAction.of_wp
  intro initial
  refine hoare_consequence
    (P := fun w => RetainsView initial (view w))
    (Q := fun _ w => RetainsView initial (view w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    dsimp only [id] at h
    rw [h]
    exact RetainsView.refl _
  rw [wgXmitSource_eq]
  unfold wgXmitSource WG.andM
  material_lower
  try unfold skipCutSites
  try unfold envOk
  repeat' first
    | traffic_join
    | (index_material_head lookupDst; exact (lookupDst_material _ _).wp (RetainsView initial))
    | (index_material_head xmitTrim; exact (xmitTrim_material _).wp (RetainsView initial))
    | (index_material_head xmitSplice; exact (xmitSplice_material _ _).wp (RetainsView initial))
    | (index_material_head sendStagedPackets; exact (sendStagedPackets_material _).wp initial)
    | (index_material_head loopbackSend; exact (sameView_of_sameWG (project := id) (Leanux.Proofs.WG.Queues.loopbackSend_kernel _ _)).wp (RetainsView initial))
    | traffic_basic (RetainsView initial)


private theorem material_product_lift (a : WG.M α) (P : View → Prop)
    (h : Hoare a (fun w => P (view w)) (fun _ w => P (view w))) :
    Hoare (liftWG a) (fun w => P (view w.wg)) (fun _ w => P (view w.wg)) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi hr
  rw [liftWG_run] at hr
  cases he : (a.run w.wg).run w.ambient with
  | error e => simp [he,Except.map] at hr
  | ok out =>
    rcases out with ⟨⟨y,g⟩,ambient⟩
    simp [he,Except.map] at hr
    rcases hr with ⟨rfl,rfl⟩
    exact (hoare_iff_run_ambient _ _ _).mp h _ _ _ _ _ hi he

elab "traffic_product_lift " initial:term : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  let args := target.getAppArgs
  unless (target.isAppOf ``Hoare || target.isAppOf ``Triple) && args.size ≥ 3 do
    throwError "not an endpoint contract"
  let preType ← whnf (← inferType args[args.size-2]!)
  let .forallE _ state _ _ := preType | throwError "not a state predicate"
  unless state.isConstOf ``World do throwError "not a product-state contract"
  let action := args[args.size-3]!.consumeMData
  let .const name _ := action.getAppFn | throwError "not a lifted action"
  unless [``monadLift,``MonadLiftT.monadLift,``MonadLift.monadLift,``liftWG,``liftAmbient].contains name do
    throwError "not a product lift"
  let source := action.getAppArgs.back!
  let saved ← saveState
  try
    let proof ← mkAppM ``productAmbient_spec #[source,args[args.size-2]!]
    replaceMainGoal (← goal.apply proof)
    evalTactic (← `(tactic| exact fun _ _ hi => hi))
  catch _ =>
    saved.restore
    let i ← elabTerm initial (some (mkConst ``View))
    let predicate ← mkAppM ``RetainsView #[i]
    let trial ← saveState
    try
      let routed ← mkAppM ``liftRouting #[source]
      let proof ← mkAppM ``material_product_lift #[routed,predicate]
      replaceMainGoal (← goal.apply proof)
    catch _ =>
      trial.restore
      let proof ← mkAppM ``material_product_lift #[source,predicate]
      replaceMainGoal (← goal.apply proof)

elab "traffic_local " callback:term : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  let args := target.getAppArgs
  unless (target.isAppOf ``Hoare || target.isAppOf ``Triple) && args.size ≥ 3 do
    throwError "not an endpoint contract"
  let action := args[args.size-3]!.consumeMData
  let expected ← elabTerm callback none
  unless Expr.equal action.getAppFn expected do throwError "not this callback"

macro "traffic_product_basic " initial:term : tactic => `(tactic|
  first
    | unfold Preserves
    | material_join
    | material_join_use
    | traffic_join
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | traffic_product_lift $initial
    | (first | index_material_head get | index_material_head MonadStateOf.get
       exact hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2))
    | (index_material_head getWG; unfold getWG)
    | (index_material_head getEnv; unfold getEnv)
    | (index_material_head modifyEnv; unfold modifyEnv)
    | (index_material_head Leanux.Env.Stack.excluded; unfold Leanux.Env.Stack.excluded; material_lower)
    | (index_material_head modify; apply hoare_modify; intro w hw; exact hw)
    | (first | index_material_head throw | index_material_head MonadExceptOf.throw
       apply (hoare_iff_run _ _ _).mpr
       intro w x v hi hr
       cases hr)
    | (index_material_head ForIn.forIn
       apply list_view_spec (fun w : World => view w.wg) (RetainsView $initial)
       intro x b)
    | (index_material_head discard
       apply discard_view_spec (fun w : World => view w.wg) (RetainsView $initial))
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match
    | contradiction
    | traffic_basic (RetainsView $initial))

theorem reply4_material (dst : Nat) (bytes : List UInt8) :
    ProductRetainsCall (Leanux.Env.Stack.reply4 dst bytes) := by
  intro initial
  refine hoare_consequence (P := fun w => RetainsView initial (view w.wg))
    (Q := fun _ w => RetainsView initial (view w.wg)) ?_
    (fun w h => by change view w.wg = initial at h; rw [h]; exact RetainsView.refl _) (fun _ _ h => h)
  unfold Leanux.Env.Stack.reply4
  material_lower
  try unfold skipCut
  repeat' first
    | (index_material_head wgXmit; exact (wgXmit_material _ _ _ _).wp initial)
    | traffic_product_basic initial

theorem receive4_material (bytes : List UInt8) :
    ProductRetainsCall (Leanux.Env.Stack.receive4 bytes) := by
  intro initial
  refine hoare_consequence (P := fun w => RetainsView initial (view w.wg))
    (Q := fun _ w => RetainsView initial (view w.wg)) ?_
    (fun w h => by change view w.wg = initial at h; rw [h]; exact RetainsView.refl _) (fun _ _ h => h)
  unfold Leanux.Env.Stack.receive4 Leanux.Env.Stack.excluded
  material_lower
  repeat' first
    | (index_material_head Leanux.Env.Stack.reply4; exact ProjectedRetainsCall.wp (reply4_material _ _) initial)
    | traffic_product_basic initial

theorem deliverInner_material (bytes : List UInt8) : ProductRetainsCall (Leanux.Env.deliverInner bytes) := by
  intro initial
  refine hoare_consequence (P := fun w => RetainsView initial (view w.wg))
    (Q := fun _ w => RetainsView initial (view w.wg)) ?_
    (fun w h => by change view w.wg = initial at h; rw [h]; exact RetainsView.refl _) (fun _ _ h => h)
  unfold Leanux.Env.deliverInner Leanux.Env.Stack.receive Leanux.Env.Stack.receive6
  material_lower
  repeat' first
    | (index_material_head Leanux.Env.Stack.receive4; exact ProjectedRetainsCall.wp (receive4_material _) initial)
    | traffic_product_basic initial

theorem stackForM_material (packets : List (List UInt8)) :
    ProductRetainsCall (packets.forM Leanux.Env.deliverInner) := by
  intro initial
  refine hoare_consequence (P := fun w => RetainsView initial (view w.wg))
    (Q := fun _ w => RetainsView initial (view w.wg)) ?_
    (fun w h => by change view w.wg = initial at h; rw [h]; exact RetainsView.refl _) (fun _ _ h => h)
  have one := fun bytes => ProjectedRetainsCall.wp (deliverInner_material bytes) initial
  induction packets with
  | nil => exact preserves_pure _
  | cons p ps ih =>
    simp only [List.forM_eq_forM,List.forM_cons]
    exact preserves_bind (one p) (fun _ => ih)

theorem encryptPacket_material (checksum : Packet → Leanux.M Packet)
    (hc : ∀ p, ProductRetainsCall (checksum p)) (key : KeypairId) (pkt : DataPacket) :
    ProductRetainsCall (encryptPacket checksum key pkt) := by
  intro initial
  refine hoare_consequence (P := fun w => RetainsView initial (view w.wg))
    (Q := fun _ w => RetainsView initial (view w.wg)) ?_
    (fun w h => by change view w.wg = initial at h; rw [h]; exact RetainsView.refl _) (fun _ _ h => h)
  unfold encryptPacket
  material_lower
  try unfold skipCut
  repeat' first
    | (index_material_head calculateSkbPadding; exact ((calculateSkbPadding_sameWGWorld _ _).factor view).wp (RetainsView initial))
    | (traffic_local checksum; exact ProjectedRetainsCall.wp (hc _) initial)
    | traffic_product_basic initial

private theorem encryptPoll_material : SameView view TxRing.pollSource := by
  intro initial
  unfold TxRing.pollSource
  material_lower
  repeat' traffic_basic (fun v => v = initial)

theorem encryptStep_material (checksum : Packet → Leanux.M Packet) (softirq : Leanux.M Unit)
    (hc : ∀ p, ProductRetainsCall (checksum p)) (hi : ProductRetainsCall softirq) :
    ProductRetainsCall (encryptStep checksum softirq) := by
  rw [← TxRing.stepSource_eq]
  intro initial
  refine hoare_consequence (P := fun w => RetainsView initial (view w.wg))
    (Q := fun _ w => RetainsView initial (view w.wg)) ?_
    (fun w h => by change view w.wg = initial at h; rw [h]; exact RetainsView.refl _) (fun _ _ h => h)
  unfold TxRing.stepSource
  material_lower
  repeat' first
    | (index_material_head TxRing.pollSource; exact encryptPoll_material.wp (RetainsView initial))
    | (index_material_head encryptPacket; exact ProjectedRetainsCall.wp (encryptPacket_material checksum hc _ _) initial)
    | (index_material_head enqueuePerPeerTx; exact (enqueuePerPeerTx_material _ _).wp initial)
    | (traffic_local softirq; exact ProjectedRetainsCall.wp hi initial)
    | traffic_product_basic initial

theorem encryptIter_material (checksum : Packet → Leanux.M Packet) (softirq : Leanux.M Unit)
    (need : Leanux.M Bool) (hc : ∀ p, ProductRetainsCall (checksum p))
    (hi : ProductRetainsCall softirq) (hn : ProductRetainsCall need) :
    ProductRetainsCall (encryptIter checksum softirq need) := by
  apply workerIter_material _ _ _ _ (encryptStep_material checksum softirq hc hi)
  intro initial
  refine hoare_consequence (P := fun w => RetainsView initial (view w.wg))
    (Q := fun _ w => RetainsView initial (view w.wg)) ?_
    (fun w h => by change view w.wg = initial at h; rw [h]; exact RetainsView.refl _) (fun _ _ h => h)
  material_lower
  repeat' first
    | (traffic_local need; exact ProjectedRetainsCall.wp hn initial)
    | traffic_product_basic initial

theorem actualChecksum_material (pkt : Packet) : ProductRetainsCall (Leanux.Env.checksumHelp pkt) :=
  of_view ((checksumHelp_sameWorld pkt).factor (fun w => view w.wg))

theorem decryptPacket_material (pkt : RxPacket) : RetainsCall (decryptPacket pkt) := by
  intro initial
  exact hoare_consequence
    (decrypt_spec (RetainsView initial) (fun _ _ hr hi => hi.trans hr) pkt)
    (fun w h => by change view w = initial at h; rw [h]; exact RetainsView.refl _)
    (fun _ _ h => h)

theorem counterValidate_material (kp : KeypairId) (nonce : Nat) :
    RetainsCall (counterValidate kp nonce) := by
  intro initial
  refine hoare_consequence
    (P := fun w => RetainsView initial (view w))
    (Q := fun _ w => RetainsView initial (view w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    change view w = initial at h
    rw [h]
    exact RetainsView.refl _
  unfold counterValidate WG.orM
  apply hoare_bind _ _ (getKeypair_spec (RetainsView initial) kp)
  intro k
  let P : View → Prop := fun v => RetainsView initial v ∧ keyAt v kp = some k
  have finish (counter : ReplayCounter) (b : Bool) :
      Hoare (do setKeypair kp {k with receivingCounter := counter}; pure b)
        (fun w => P (view w)) (fun _ w => RetainsView initial (view w)) := by
    apply hoare_bind _ _
    · exact hoare_consequence
        (setKeypair_spec (RetainsView initial) (fun _ _ hr hi => hi.trans hr)
          kp {k with receivingCounter := counter})
        (fun _ h => ⟨h.1,fun hv => ⟨k,h.2,hv,⟨rfl,Or.inr rfl⟩⟩⟩) (fun _ _ h => h)
    · intro _
      exact preserves_pure _
  have step {β : Type} (a : WG.M β) (f : β → WG.M Bool)
      (ha : Hoare a (fun w => P (view w)) (fun _ w => P (view w)))
      (hf : ∀ x, Hoare (f x) (fun w => P (view w)) (fun _ w => RetainsView initial (view w))) :
      Hoare (a >>= f) (fun w => P (view w)) (fun _ w => RetainsView initial (view w)) :=
    hoare_bind a f ha hf
  change Hoare _ (fun w => P (view w)) (fun _ w => RetainsView initial (view w))
  material_lower
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (index_material_head Bind.bind
       run_tac do
         let t ← getMainTarget
         let aa := t.getAppArgs
         let action := aa[aa.size-3]!
         let ba := action.getAppArgs
         unless ba[ba.size-2]!.isAppOf ``setKeypair do throwError "not final update"
       exact finish _ _)
    | (index_material_head Bind.bind; apply step)
    | (index_material_head Pure.pure
       exact hoare_consequence (preserves_pure _) (fun _ h => h.1) (fun _ _ h => h))
    | (index_material_head ite; split)
    | traffic_basic P

theorem receivedWithKeypair_material (pid : PeerId) (kp : KeypairId) :
    RetainsCall (receivedWithKeypair pid kp) := by
  intro initial
  refine hoare_consequence
    (P := fun w => RetainsView initial (view w))
    (Q := fun _ w => RetainsView initial (view w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    change view w = initial at h
    rw [h]
    exact RetainsView.refl _
  unfold receivedWithKeypair
  material_lower
  repeat' first
    | traffic_key initial
    | traffic_basic (RetainsView initial)

theorem timersHandshakeComplete_material (pid : PeerId) (site : HiddenSite) :
    SameView view (timersHandshakeComplete pid site) := by
  intro initial
  unfold timersHandshakeComplete
  material_lower
  repeat' first
    | (index_material_head delTimer; exact (delTimer_material _ _).wp (fun v => v = initial))
    | traffic_basic (fun v => v = initial)

theorem timersAnyAuthenticatedPacketReceived_material (pid : PeerId) :
    SameView view (timersAnyAuthenticatedPacketReceived pid) := delTimer_material pid .newHandshake

theorem timersDataReceived_material (pid : PeerId) : SameView view (timersDataReceived pid) := by
  intro initial
  unfold timersDataReceived
  material_lower
  repeat' first
    | (index_material_head modPeerTimer; exact (modPeerTimer_material _ _ _ _).wp (fun v => v = initial))
    | traffic_basic (fun v => v = initial)

theorem keepKeyFreshRx_material (pid : PeerId) : RetainsCall (keepKeyFreshRx pid) := by
  intro initial
  refine hoare_consequence
    (P := fun w => RetainsView initial (view w))
    (Q := fun _ w => RetainsView initial (view w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    change view w = initial at h
    rw [h]
    exact RetainsView.refl _
  unfold keepKeyFreshRx
  material_lower
  repeat' first
    | (index_material_head sendQueuedHandshakeInitiation; exact (sendQueuedHandshakeInitiation_material _ _).wp initial)
    | traffic_basic (RetainsView initial)

theorem dishonest_material (why : Dishonest) : SameView view (dishonest why) :=
  modifyDev_material _ (fun d => by cases why <;> rfl)

theorem updateRxStats_material (pid : PeerId) (len : Nat) :
    SameView view (updateRxStats pid len) := by
  intro initial
  unfold updateRxStats
  repeat' traffic_basic (fun v => v = initial)

theorem consumeDataDone_material (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    RetainsCall (consumeDataDone pid pkt endpoint) := by
  intro initial
  refine hoare_consequence
    (P := fun w => RetainsView initial (view w))
    (Q := fun _ w => RetainsView initial (view w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    change view w = initial at h
    rw [h]
    exact RetainsView.refl _
  unfold consumeDataDone
  material_lower
  repeat' first
    | traffic_join
    | (index_material_head setPeerEndpoint; exact (setPeerEndpoint_material _ _).wp (RetainsView initial))
    | (index_material_head receivedWithKeypair; exact (receivedWithKeypair_material _ _).wp initial)
    | (index_material_head timersHandshakeComplete; exact (timersHandshakeComplete_material _ _).wp (RetainsView initial))
    | (index_material_head sendStagedPackets; exact (sendStagedPackets_material _).wp initial)
    | (index_material_head keepKeyFreshRx; exact (keepKeyFreshRx_material _).wp initial)
    | (index_material_head timersAnyAuthenticatedPacketReceived; exact (timersAnyAuthenticatedPacketReceived_material _).wp (RetainsView initial))
    | (index_material_head timersTraversal; exact (timersTraversal_material _).wp (RetainsView initial))
    | (index_material_head timersDataReceived; exact (timersDataReceived_material _).wp (RetainsView initial))
    | (index_material_head updateRxStats; exact (updateRxStats_material _ _).wp (RetainsView initial))
    | (index_material_head dishonest; exact (dishonest_material _).wp (RetainsView initial))
    | (index_material_head inetEcnDecapsulate; exact (sameView_of_sameWG (project := id) (inetEcnDecapsulate_sameWGStore _ _ _)).wp (RetainsView initial))
    | (index_material_head lookupSrc; exact (lookupSrc_material _ _).wp (RetainsView initial))
    | traffic_basic (RetainsView initial)

private theorem peekRxQueue_material (pid : PeerId) : SameView view (peekRxQueue pid) := by
  intro initial
  unfold peekRxQueue
  repeat' first
    | (index_material_head PrevQueue.peek; exact (sameView_of_sameWG (project := id) (prevQueuePeek_sameWGStore _)).wp (fun v => v = initial))
    | traffic_basic (fun v => v = initial)

private theorem dropRxQueue_material (pid : PeerId) : SameView view (dropRxQueue pid) := by
  intro initial
  unfold dropRxQueue
  repeat' traffic_basic (fun v => v = initial)

private theorem completeRxQueue_material (pid : PeerId) : SameView view (completeRxQueue pid) := by
  intro initial
  unfold completeRxQueue
  repeat' traffic_basic (fun v => v = initial)

theorem groNormalList_material (cb : List (List UInt8) → Leanux.M Unit)
    (hc : ∀ xs, ProductRetainsCall (cb xs)) (g : GroState) :
    ProductRetainsCall (groNormalList cb g) := by
  intro initial
  refine hoare_consequence (P := fun w => RetainsView initial (view w.wg))
    (Q := fun _ w => RetainsView initial (view w.wg)) ?_
    (fun w h => by change view w.wg = initial at h; rw [h]; exact RetainsView.refl _) (fun _ _ h => h)
  unfold groNormalList
  repeat' first
    | (traffic_local cb; exact ProjectedRetainsCall.wp (hc _) initial)
    | traffic_product_basic initial

theorem groNormalOne_material (cb : List (List UInt8) → Leanux.M Unit)
    (hc : ∀ xs, ProductRetainsCall (cb xs)) (g : GroState) (pkt : List UInt8) (segs : Nat) :
    ProductRetainsCall (groNormalOne cb g pkt segs) := by
  intro initial
  refine hoare_consequence (P := fun w => RetainsView initial (view w.wg))
    (Q := fun _ w => RetainsView initial (view w.wg)) ?_
    (fun w h => by change view w.wg = initial at h; rw [h]; exact RetainsView.refl _) (fun _ _ h => h)
  unfold groNormalOne
  repeat' first
    | (index_material_head groNormalList; exact ProjectedRetainsCall.wp (groNormalList_material cb hc _) initial)
    | traffic_product_basic initial

theorem napiGroReceive_material (cb : List (List UInt8) → Leanux.M Unit)
    (hc : ∀ xs, ProductRetainsCall (cb xs)) (g : GroState) (pkt : List UInt8) :
    ProductRetainsCall (napiGroReceive cb g pkt) := by
  intro initial
  refine hoare_consequence (P := fun w => RetainsView initial (view w.wg))
    (Q := fun _ w => RetainsView initial (view w.wg)) ?_
    (fun w h => by change view w.wg = initial at h; rw [h]; exact RetainsView.refl _) (fun _ _ h => h)
  unfold napiGroReceive
  material_lower
  repeat' first
    | (index_material_head groNormalOne; exact ProjectedRetainsCall.wp (groNormalOne_material cb hc _ _ _) initial)
    | traffic_product_basic initial

theorem napiGroFlushAll_material (cb : List (List UInt8) → Leanux.M Unit)
    (hc : ∀ xs, ProductRetainsCall (cb xs)) (g : GroState) :
    ProductRetainsCall (napiGroFlushAll cb g) := by
  intro initial
  refine hoare_consequence (P := fun w => RetainsView initial (view w.wg))
    (Q := fun _ w => RetainsView initial (view w.wg)) ?_
    (fun w h => by change view w.wg = initial at h; rw [h]; exact RetainsView.refl _) (fun _ _ h => h)
  unfold napiGroFlushAll
  repeat' first
    | (index_material_head groNormalOne; exact ProjectedRetainsCall.wp (groNormalOne_material cb hc _ _ _) initial)
    | (index_material_head groNormalList; exact ProjectedRetainsCall.wp (groNormalList_material cb hc _) initial)
    | traffic_product_basic initial

theorem rxPoll_material (pid : PeerId) (budget : Nat) (cb : List (List UInt8) → Leanux.M Unit)
    (hc : ∀ xs, ProductRetainsCall (cb xs)) : ProductRetainsCall (rxPoll pid budget cb) := by
  rw [← rxPollGrouped_eq]
  intro initial
  refine hoare_consequence (P := fun w => RetainsView initial (view w.wg))
    (Q := fun _ w => RetainsView initial (view w.wg)) ?_
    (fun w h => by change view w.wg = initial at h; rw [h]; exact RetainsView.refl _) (fun _ _ h => h)
  unfold rxPollGrouped
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range']
  material_lower
  repeat' first
    | traffic_product_basic initial
    | (index_material_head peekRxQueue; exact (peekRxQueue_material _).wp (RetainsView initial))
    | (index_material_head dropRxQueue; exact (dropRxQueue_material _).wp (RetainsView initial))
    | (index_material_head completeRxQueue; exact (completeRxQueue_material _).wp (RetainsView initial))
    | (index_material_head counterValidate; exact (counterValidate_material _ _).wp initial)
    | (index_material_head endpointFromSkb; exact (sameView_of_sameWG (project := id) (endpointFromSkb_sameWGStore _)).wp (RetainsView initial))
    | (index_material_head consumeDataDone; exact (consumeDataDone_material _ _ _).wp initial)
    | (index_material_head napiGroReceive; exact ProjectedRetainsCall.wp (napiGroReceive_material cb hc _ _) initial)
    | (index_material_head napiGroFlushAll; exact ProjectedRetainsCall.wp (napiGroFlushAll_material cb hc _) initial)
    | traffic_key initial

theorem actualRxPoll_material (pid : PeerId) (budget : Nat) :
    ProductRetainsCall (rxPoll pid budget (fun xs => xs.forM Leanux.Env.deliverInner)) :=
  rxPoll_material pid budget _ stackForM_material

theorem enqueuePerPeerRx_material (irq : Leanux.M Unit) (hi : ProductRetainsCall irq)
    (id : SkbId) (state : PacketState) : ProductRetainsCall (enqueuePerPeerRx irq id state) := by
  intro initial
  refine hoare_consequence (P := fun w => RetainsView initial (view w.wg))
    (Q := fun _ w => RetainsView initial (view w.wg)) ?_
    (fun w h => by change view w.wg = initial at h; rw [h]; exact RetainsView.refl _) (fun _ _ h => h)
  unfold enqueuePerPeerRx
  material_lower
  repeat' first
    | (traffic_local irq; exact ProjectedRetainsCall.wp hi initial)
    | traffic_product_basic initial

/-- The fixed consume-data caller supplies a native IRQ continuation. The
original unrestricted product contract remains above. -/
theorem enqueuePerPeerRx_material_native (irq : WG.M Unit) (hi : RetainsCall irq)
    (id : SkbId) (state : PacketState) : RetainsCall (enqueuePerPeerRx irq id state) := by
  intro initial
  refine hoare_consequence
    (P := fun w => RetainsView initial (view w))
    (Q := fun _ w => RetainsView initial (view w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    change view w = initial at h
    rw [h]
    exact RetainsView.refl _
  unfold enqueuePerPeerRx
  material_lower
  repeat' first
    | (traffic_local irq; exact hi.wp initial)
    | traffic_basic (RetainsView initial)

private theorem decryptPoll_material : SameView view RxRing.pollSource := by
  intro initial
  unfold RxRing.pollSource
  material_lower
  repeat' traffic_basic (fun v => v = initial)

theorem decryptStep_material (softirq irq : Leanux.M Unit)
    (hs : ProductRetainsCall softirq) (hi : ProductRetainsCall irq) :
    ProductRetainsCall (decryptStep softirq irq) := by
  rw [← RxRing.stepSource_eq]
  intro initial
  refine hoare_consequence (P := fun w => RetainsView initial (view w.wg))
    (Q := fun _ w => RetainsView initial (view w.wg)) ?_
    (fun w h => by change view w.wg = initial at h; rw [h]; exact RetainsView.refl _) (fun _ _ h => h)
  unfold RxRing.stepSource
  material_lower
  repeat' first
    | (index_material_head RxRing.pollSource; exact decryptPoll_material.wp (RetainsView initial))
    | (index_material_head decryptPacket; exact (decryptPacket_material _).wp initial)
    | (index_material_head enqueuePerPeerRx; exact ProjectedRetainsCall.wp (enqueuePerPeerRx_material irq hi _ _) initial)
    | (traffic_local softirq; exact ProjectedRetainsCall.wp hs initial)
    | traffic_product_basic initial

theorem decryptIter_material (softirq irq : Leanux.M Unit) (need : Leanux.M Bool)
    (hs : ProductRetainsCall softirq) (hi : ProductRetainsCall irq) (hn : ProductRetainsCall need) :
    ProductRetainsCall (decryptIter softirq irq need) := by
  apply workerIter_material _ _ _ _ (decryptStep_material softirq irq hs hi)
  intro initial
  refine hoare_consequence (P := fun w => RetainsView initial (view w.wg))
    (Q := fun _ w => RetainsView initial (view w.wg)) ?_
    (fun w h => by change view w.wg = initial at h; rw [h]; exact RetainsView.refl _) (fun _ _ h => h)
  material_lower
  repeat' first
    | (traffic_local need; exact ProjectedRetainsCall.wp hn initial)
    | traffic_product_basic initial

theorem enqueuePerDeviceAndPeerRx_material (id : SkbId) :
    SameView view (enqueuePerDeviceAndPeerRx id) := by
  intro initial
  unfold enqueuePerDeviceAndPeerRx cpumaskNextOnlineFrom queueDeviceWork
  material_lower
  repeat' traffic_basic (fun v => v = initial)

theorem consumeData_material (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    RetainsCall (consumeData msg src ds) := by
  intro initial
  refine hoare_consequence
    (P := fun w => RetainsView initial (view w))
    (Q := fun _ w => RetainsView initial (view w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    change view w = initial at h
    rw [h]
    exact RetainsView.refl _
  unfold consumeData keypairGetNull
  material_lower
  repeat' first
    | (index_material_head indexLookup; exact (indexLookup_retains _ _).wp (RetainsView initial) (fun _ _ hr hi => hi.trans hr))
    | (index_material_head enqueuePerDeviceAndPeerRx; exact (enqueuePerDeviceAndPeerRx_material _).wp (RetainsView initial))
    | (index_material_head enqueuePerPeerRx
       exact (enqueuePerPeerRx_material_native (pure ()) (of_view (SameView.pure view ())) _ _).wp initial)
    | traffic_key initial
    | traffic_basic (RetainsView initial)

theorem cpumaskNextOnline_material : SameView view cpumaskNextOnline := by
  intro initial
  unfold cpumaskNextOnline
  material_lower
  repeat' traffic_basic (fun v => v = initial)

theorem packetReceive_material (msg : List UInt8) (src : SkbSource) :
    RetainsCall (packetReceive msg src) := by
  intro initial
  refine hoare_consequence
    (P := fun w => RetainsView initial (view w))
    (Q := fun _ w => RetainsView initial (view w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    change view w = initial at h
    rw [h]
    exact RetainsView.refl _
  unfold packetReceive queueDeviceWork
  material_lower
  repeat' first
    | (index_material_head prepareSkbHeader; exact ((prepareSkbHeader_sameWGWorld _).factor view).wp (RetainsView initial))
    | (index_material_head ipTunnelGetDsfield; exact ((ipTunnelGetDsfield_sameWGWorld _ _).factor view).wp (RetainsView initial))
    | (index_material_head consumeData; exact (consumeData_material _ _ _).wp initial)
    | (index_material_head cpumaskNextOnline; exact cpumaskNextOnline_material.wp (RetainsView initial))
    | traffic_basic (RetainsView initial)

theorem wgReceive_material (msg : List UInt8) (src : SkbSource) :
    RetainsCall (wgReceive msg src) := by
  intro initial
  refine hoare_consequence
    (P := fun w => RetainsView initial (view w))
    (Q := fun _ w => RetainsView initial (view w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    change view w = initial at h
    rw [h]
    exact RetainsView.refl _
  unfold wgReceive
  material_lower
  repeat' first
    | (index_material_head packetReceive; exact (packetReceive_material _ _).wp initial)
    | traffic_basic (RetainsView initial)

theorem runWorker_material (worker : Worker) (body : Leanux.M Unit)
    (hb : ProductRetainsCall body) : ProductRetainsCall (Env.runWorker worker body) := by
  intro initial
  refine hoare_consequence (P := fun w => RetainsView initial (view w.wg))
    (Q := fun _ w => RetainsView initial (view w.wg)) ?_
    (fun w h => by change view w.wg = initial at h; rw [h]; exact RetainsView.refl _) (fun _ _ h => h)
  unfold Env.runWorker
  material_lower
  repeat' first
    | (traffic_local body; exact ProjectedRetainsCall.wp hb initial)
    | traffic_product_basic initial

private theorem pendingPolls_material (pending : List PeerId) :
    ProductRetainsCall (do
      for pid in pending do
        discard <| rxPoll pid NAPI_POLL_WEIGHT (fun xs => xs.forM Env.deliverInner)) := by
  intro initial
  refine hoare_consequence (P := fun w => RetainsView initial (view w.wg))
    (Q := fun _ w => RetainsView initial (view w.wg)) ?_
    (fun w h => by change view w.wg = initial at h; rw [h]; exact RetainsView.refl _) (fun _ _ h => h)
  repeat' first
    | (index_material_head rxPoll; exact ProjectedRetainsCall.wp (actualRxPoll_material _ _) initial)
    | traffic_product_basic initial

theorem napiSoftirq_material : ProductRetainsCall Env.napiSoftirq := by
  intro initial
  refine hoare_consequence (P := fun w => RetainsView initial (view w.wg))
    (Q := fun _ w => RetainsView initial (view w.wg)) ?_
    (fun w h => by change view w.wg = initial at h; rw [h]; exact RetainsView.refl _) (fun _ _ h => h)
  unfold Env.napiSoftirq
  material_lower
  try unfold peekHiddenSite
  repeat' first
    | (index_material_head Env.runWorker
       exact ProjectedRetainsCall.wp (runWorker_material .netRx _ (pendingPolls_material _)) initial)
    | traffic_product_basic initial

/-- The second actual direct poll site runs without opening a new section. -/
theorem pollScheduledInline_material : ProductRetainsCall Env.pollScheduledInline := by
  intro initial
  refine hoare_consequence (P := fun w => RetainsView initial (view w.wg))
    (Q := fun _ w => RetainsView initial (view w.wg)) ?_
    (fun w h => by change view w.wg = initial at h; rw [h]; exact RetainsView.refl _) (fun _ _ h => h)
  unfold Env.pollScheduledInline
  material_lower
  repeat' first
    | (index_material_head rxPoll; exact ProjectedRetainsCall.wp (actualRxPoll_material _ _) initial)
    | traffic_product_basic initial

theorem napiIrqExit_material : ProductRetainsCall Env.napiIrqExit := by
  rw [← napiIrqExitSource_eq]
  intro initial
  refine hoare_consequence (P := fun w => RetainsView initial (view w.wg))
    (Q := fun _ w => RetainsView initial (view w.wg)) ?_
    (fun w h => by change view w.wg = initial at h; rw [h]; exact RetainsView.refl _) (fun _ _ h => h)
  unfold napiIrqExitSource chooseNapiHere
  material_lower
  try unfold peekHiddenSite
  repeat' first
    | (index_material_head Env.napiSoftirq; exact ProjectedRetainsCall.wp napiSoftirq_material initial)
    | traffic_product_basic initial

theorem actualEncryptStep_material : ProductRetainsCall (encryptStep Env.checksumHelp Env.napiSoftirq) :=
  encryptStep_material _ _ actualChecksum_material napiSoftirq_material

theorem actualEncryptIter_material :
    ProductRetainsCall (encryptIter Env.checksumHelp Env.napiSoftirq (Env.condResched .encryptWorker)) := by
  apply encryptIter_material _ _ _ actualChecksum_material napiSoftirq_material
  intro initial
  refine hoare_consequence (P := fun w => RetainsView initial (view w.wg))
    (Q := fun _ w => RetainsView initial (view w.wg)) ?_
    (fun w h => by change view w.wg = initial at h; rw [h]; exact RetainsView.refl _) (fun _ _ h => h)
  unfold Env.condResched
  material_lower
  try unfold peekHiddenSite
  repeat' traffic_product_basic initial

theorem actualDecryptStep_material : ProductRetainsCall (decryptStep Env.napiSoftirq Env.napiIrqExit) :=
  decryptStep_material _ _ napiSoftirq_material napiIrqExit_material

theorem actualDecryptIter_material :
    ProductRetainsCall (decryptIter Env.napiSoftirq Env.napiIrqExit (Env.condResched .decryptWorker)) := by
  apply decryptIter_material _ _ _ napiSoftirq_material napiIrqExit_material
  intro initial
  refine hoare_consequence (P := fun w => RetainsView initial (view w.wg))
    (Q := fun _ w => RetainsView initial (view w.wg)) ?_
    (fun w h => by change view w.wg = initial at h; rw [h]; exact RetainsView.refl _) (fun _ _ h => h)
  unfold Env.condResched
  material_lower
  try unfold peekHiddenSite
  repeat' traffic_product_basic initial

theorem actualTxIter_material (pid : PeerId) :
    ProductRetainsCall (txIter pid (Env.condResched .txWorker)) := by
  apply txIter_material _ _
  intro initial
  refine hoare_consequence (P := fun w => RetainsView initial (view w.wg))
    (Q := fun _ w => RetainsView initial (view w.wg)) ?_
    (fun w h => by change view w.wg = initial at h; rw [h]; exact RetainsView.refl _) (fun _ _ h => h)
  unfold Env.condResched
  material_lower
  try unfold peekHiddenSite
  repeat' traffic_product_basic initial

end Leanux.Proofs.WG.Origins.Retaining
