import Leanux.Proofs.WG.Queues.CurrentSlots
import Leanux.Proofs.WG.Queues.HolderWorkFrames

/-! Session allocation and rotation preserve the existing peer-credit account.
Nullable ownership and allocation bounds are explicit input facts; their
endpoint forms come from the same actual session, including normal refusal. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.SessionCarrier
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders

def view (w : WGWorld) := (protectView w,stableView w,passiveView w)

private theorem store {α : Type} {action : WG.M α} (same : SameWGStore action) :
    SameView view action := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b hr
  have eq := (ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b hr
  have dev : v.dev = w.dev := congrArg WGStoreView.dev eq
  have sock7 : v.nlSock7 = w.nlSock7 := congrArg WGStoreView.nlSock7 eq
  have sock8 : v.nlSock8 = w.nlSock8 := congrArg WGStoreView.nlSock8 eq
  unfold view protectView RxCredits.handoffTxView
  simp only [peerView,rxView,sendView,
    stableView,RxRing.nativeCell,passiveView,dev,sock7,sock8]

private theorem modify_frame (f : Device → Device)
    (epoch : ∀ d,(f d).ifindex=d.ifindex)
    (peers : ∀ d,(f d).peers=d.peers)
    (rx : ∀ d,(f d).rxSkbs=d.rxSkbs)
    (ring : ∀ d,(f d).decryptQueue=d.decryptQueue)
    (base : ∀ d,(f d).peerList=d.peerList)
    (send : ∀ d,(f d).sendWorkQueue=d.sendWorkQueue)
    (clear : ∀ d,(f d).clearWorkQueue=d.clearWorkQueue) : SameView view (modifyDev f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b hr
  cases hr
  unfold view protectView RxCredits.handoffTxView
  simp only [peerView,rxView,sendView,
    stableView,RxRing.nativeCell,passiveView,Option.map_map,Option.bind_map,
    Function.comp_def,epoch,peers,rx,ring,base,send,clear]

private theorem keypairPut_view (kid : Option KeypairId) (now : Bool) :
    SameView view (keypairPut kid now) := by
  have passive : SameView passiveView (keypairPut kid now) := by
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a result v b hr
    exact ((hoare_iff_run_ambient _ _ _).mp (HolderWorkFrames.keypairPut_frame kid now w)
      w a result v b (Frame.refl w) hr).passive
  exact (keypairPut_protect kid now).product ((stable_keypairPut kid now).product passive)

private theorem modifyPeer_view (pid : PeerId) (f : Peer → Peer)
    (credit : ∀ p,protectCell (f p)=protectCell p)
    (napi : ∀ p,(f p).napiScheduled=p.napiScheduled) :
    SameView view ((pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b hr
  change ((getPeer pid >>= fun p => setPeer pid (f p)).run w).run a = .ok ((result,v),b) at hr
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨p,read,c,getter,write⟩ := hr
  obtain ⟨readEq,timeEq,d,hd,hp⟩ := getPeer_normal pid w read p a c getter
  subst read
  subst c
  cases write
  have protect := protect_set_same (w := w) hd hp (credit p)
  have fields : (f p).internalId=p.internalId ∧ (f p).refcount=p.refcount ∧
      (f p).rxQueue=p.rxQueue ∧ (f p).txQueue.all=p.txQueue.all := by
    simpa only [protectCell,Prod.mk.injEq] using credit p
  simp only [view,hd,Option.map_some,protect]
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · simp only [stableView,RxRing.nativeCell,rxView,hd,Option.map_some,Option.bind_some]
    congr 2
    funext q
    by_cases same : pid=q <;> simp_all [Std.TreeMap.getElem?_insert]
  · simp only [passiveView,hd,Option.map_some]

macro "session_credit_step " initial:term : tactic => `(tactic| first
  | rxstack_preserves_join
  | (rx_retention_head getPeer
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a p v b hi hr
     simpa only [(getPeer_normal _ w v p a b hr).1] using hi)
  | (rx_retention_head getDev; exact (store getDev_sameWGStore).wp (fun s => s=$initial))
  | (rx_retention_head getKeypair
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a k v b hi hr
     simpa only [(KeyTimes.getKeypair_return _ w v k a b hr).1] using hi)
  | (rx_retention_head setKeypair; unfold setKeypair)
  | (rx_retention_head keypairPut; exact (keypairPut_view _ _).wp (fun s => s=$initial))
  | (rx_retention_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ _)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (allocation_release_lift_from IndexM
     apply hoare_liftIndex
     intro w d table hi hd
     unfold view protectView RxCredits.handoffTxView at hi ⊢
     simpa only [peerView,rxView,sendView,stableView,RxRing.nativeCell,passiveView,hd,Option.map_some,Option.bind_some] using hi)
  | (rx_retention_head modifyDev
     apply (modify_frame _ ?_ ?_ ?_ ?_ ?_ ?_ ?_).wp (fun s => s=$initial)
     all_goals intro d; rfl)
  | (rx_retention_head modify; apply hoare_modify; intro w hi; exact hi)
  | (rx_retention_head get; exact hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2))
  | rx_retention_step)

theorem keypairCreate_view (word : Option PeerId) : SameView view (keypairCreate word) := by
  intro initial
  change Preserves (fun w => view w=initial) _
  unfold keypairCreate
  simp (config := {zeta := false}) only [hiddenAlloc,branch]
  repeat' session_credit_step initial

theorem deriveKeys_view (kid : KeypairId) (initiator : Bool) (chain : List UInt8) :
    SameView view (deriveKeys kid initiator chain) := by
  intro initial
  change Preserves (fun w => view w=initial) _
  unfold deriveKeys
  simp (config := {zeta := false}) only [hiddenClock64]
  repeat' first
    | (rx_retention_head kdf; exact (Framing.kdf_sameWGWorld _ _ _ _).wp (fun w => view w=initial))
    | (rx_retention_head kdfOut; exact (Framing.kdfOut_sameWGWorld _ _).wp (fun w => view w=initial))
    | session_credit_step initial

theorem addNewKeypair_view (pid : PeerId) (kid : KeypairId) :
    SameView view (addNewKeypair pid kid) := by
  intro initial
  change Preserves (fun w => view w=initial) _
  unfold addNewKeypair
  simp (config := {zeta := false}) only [branch]
  repeat' session_credit_step initial
  all_goals apply (modifyPeer_view _ _ ?_ ?_).wp (fun s => s=initial)
  all_goals intro p; rfl

theorem handshakeZero_view (pid : PeerId) : SameView view (handshakeZero pid) := by
  unfold handshakeZero
  exact modifyPeer_view pid _ (fun _ => rfl) (fun _ => rfl)

theorem beginSession_view (pid : PeerId) : SameView view (beginSession pid) := by
  intro initial
  change Preserves (fun w => view w=initial) _
  unfold beginSession WG.andM IndexOwner.peerWord
  simp (config := {zeta := false}) only [branch,invariant,unsupported]
  repeat' first
    | (rx_retention_head keypairCreate; exact (keypairCreate_view _).wp (fun s => s=initial))
    | (rx_retention_head deriveKeys; exact (deriveKeys_view _ _ _).wp (fun s => s=initial))
    | (rx_retention_head handshakeZero; exact (handshakeZero_view _).wp (fun s => s=initial))
    | (rx_retention_head addNewKeypair; exact (addNewKeypair_view _ _).wp (fun s => s=initial))
    | session_credit_step initial

/-- The actual session supplies endpoint key compatibility from explicit
entry bounds and nullable ownership. All supplied peer loans remain charged,
including allocation refusal and the normal false branch. -/
theorem beginSession_normal (pid : PeerId)
    (hi : CarrierState cs loans w) (stable : StableRx cs w)
    (configured : ConfiguredIdentity.Inv w) (owners : OwnerBounds.Carrier w)
    (slots : CurrentSlots.Inv w) (a b : Ambient)
    (run : ((beginSession pid).run w).run a = .ok ((result,v),b)) :
    CarrierState cs loans v ∧ StableRx cs v ∧ ConfiguredIdentity.Inv v ∧
      OwnerBounds.Carrier v ∧ CurrentSlots.Inv v := by
  have support := (hoare_iff_run_ambient _ _ _).mp (OwnerCreation.beginSession_preserves pid)
    w a result v b ⟨configured,owners⟩ run
  have currents := (hoare_iff_run_ambient _ _ _).mp (CurrentSlots.beginSession_preserves pid)
    w a result v b ⟨slots,configured⟩ run
  have frame := (ProjectedAction.iff_run_ambient _ _ _).mp (beginSession_view pid)
    w a result v b run
  have credit := congrArg Prod.fst frame
  have peer := congrArg Prod.fst credit
  have rx := congrArg (fun s => s.2.1) credit
  refine ⟨⟨inventory_view hi.inventory rx,queueOwners_view hi.queues peer,
    protected_view hi.funded peer,support.2.compatible,(CurrentSlots.current currents).compatible⟩,
    stable.view (congrArg (fun s => s.2.1) frame),support.1,support.2,currents⟩

/-- Session rotation changes no durable-holder list or logical TX queue.
The complete account and any caller's existing temporary loans are retained. -/
theorem beginSession_funded (pid : PeerId) {holders : DurableHolders}
    (hi : holders.Funded cs loans w) (stable : StableRx cs w)
    (configured : ConfiguredIdentity.Inv w) (owners : OwnerBounds.Carrier w)
    (slots : CurrentSlots.Inv w) (a b : Ambient)
    (run : ((beginSession pid).run w).run a = .ok ((result,v),b)) :
    holders.Funded cs loans v ∧ StableRx cs v ∧ ConfiguredIdentity.Inv v ∧
      OwnerBounds.Carrier v ∧ CurrentSlots.Inv v := by
  have result := beginSession_normal pid hi.carriers stable configured owners slots a b run
  have frame := (ProjectedAction.iff_run_ambient _ _ _).mp (beginSession_view pid)
    w a _ v b run
  have credit := congrArg Prod.fst frame
  have exactFrame : Frame w v := by
    refine ⟨congrArg (fun s => s.2.2) frame,congrArg (fun s => s.2.2.2) credit,?_⟩
    intro q batches found
    have queues : RxCredits.handoffTxView v q = RxCredits.handoffTxView w q :=
      congrFun (congrArg (fun s => s.2.2.1) credit) q
    exact queues ▸ found
  exact ⟨⟨hi.aligned.frame exactFrame,result.1⟩,result.2⟩

/-- The original lifetime observer has the same normal endpoint and account,
for arbitrary incoming history and both actual Ambient endpoints. -/
theorem beginSession_observed (pid : PeerId) {holders : DurableHolders}
    (hi : holders.Funded cs loans w) (stable : StableRx cs w)
    (configured : ConfiguredIdentity.Inv w) (owners : OwnerBounds.Carrier w)
    (slots : CurrentSlots.Inv w) (history : List LifetimeEvent) (a b : Ambient)
    (run : (runStatePrefix (beginSessionPrefix pid) w a history).1 = .ok ((result,v),b)) :
    holders.Funded cs loans v ∧ StableRx cs v ∧ ConfiguredIdentity.Inv v ∧
      OwnerBounds.Carrier v ∧ CurrentSlots.Inv v :=
  beginSession_funded pid hi stable configured owners slots a b
    ((beginSessionPrefix_erases pid w a history).symm.trans run)

end Leanux.Proofs.WG.Queues.RxCredits.SessionCarrier
