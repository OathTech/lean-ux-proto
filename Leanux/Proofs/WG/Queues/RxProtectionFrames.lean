import Leanux.Proofs.WG.Queues.RxIngressProtection
import Leanux.Proofs.WG.Packets.AffiliationCuts
import Leanux.Proofs.WG.Packets.RoutingCuts

/-! Local reference protection uses the same RX ledger throughout an actual
normal call. Key compatibility is independent of validity; erased keys and NULL
words are permitted. None of these endpoint contracts assigns a World to Stop. -/
namespace Leanux.Proofs.WG.Queues.RxCredits
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
set_option pp.structureInstances false

/-- The resident word, if any, belongs to the caller or has been cleared. -/
def KeyCompatible (pid : PeerId) (kid : KeypairId) (w : World) : Prop :=
  ∀ d k, w.k.wg = some d → d.keypairs[kid]? = some k → Affiliation.Compatible k.peer pid

def CurrentCompatible (pid : PeerId) (w : World) : Prop :=
  ∀ d p kid, w.k.wg = some d → d.peers[pid]? = some p → p.keypairCurrent = some kid →
    KeyCompatible pid kid w

def baseView (w : World) := (w.k.wg.map (·.ifindex), fun pid : PeerId =>
  (w.k.wg.bind fun d => d.peers[pid]?).map fun p => (p.internalId,p.rxQueue))
def handoffTxView (w : World) := fun pid : PeerId =>
  (w.k.wg.bind fun d => d.peers[pid]?).map fun p => p.txQueue.all
def sendView (w : World) := w.k.wg.map (·.sendWorkQueue)
def protectView (w : World) := (peerView w,rxView w,handoffTxView w,sendView w)

structure TxHandoff where
  owner : Owner
  item : List SkbId
  deriving DecidableEq

/-- Typed durable references: one per actual appended TX batch/send-work item.
Ring aliases, individual TX packets and GRO bytes contribute no further charge. -/
structure HandoffDelta where
  tx : List TxHandoff := []
  send : List Owner := []
  deriving DecidableEq

def HandoffDelta.owners (d : HandoffDelta) : List Owner := d.tx.map (·.owner) ++ d.send
def HandoffDelta.items (d : HandoffDelta) (pid : PeerId) : List (List SkbId) :=
  (d.tx.filter fun e => e.owner.slot == pid).map (·.item)
def HandoffDelta.append (a b : HandoffDelta) : HandoffDelta := ⟨a.tx ++ b.tx,a.send ++ b.send⟩

/-- Exact normal-endpoint accounting, with attributed temporary references on
both sides. The equations alone permit unfunded ghost loans; the funded
transport theorem below establishes the durable-credit interpretation. -/
structure Handoff (w v : World) (before after : Reservations) (d : HandoffDelta) : Prop where
  base : baseView v = baseView w
  rx : rxView v = rxView w
  tx : ∀ pid, handoffTxView v pid = (handoffTxView w pid).map (· ++ d.items pid)
  send : sendView v = (sendView w).map (· ++ d.send.map Owner.slot)
  count : ∀ o, balance v o + before.count o = balance w o + after.count o + d.owners.count o

@[simp] theorem delta_empty_items (pid) : ({} : HandoffDelta).items pid = [] := rfl
@[simp] theorem delta_empty_owners : ({} : HandoffDelta).owners = [] := rfl
@[simp] theorem delta_append_items (a b : HandoffDelta) (pid) :
    (a.append b).items pid = a.items pid ++ b.items pid := by
  simp [HandoffDelta.items,HandoffDelta.append]
@[simp] theorem delta_append_owners_count (a b : HandoffDelta) (o) :
    (a.append b).owners.count o = a.owners.count o + b.owners.count o := by
  simp [HandoffDelta.owners,HandoffDelta.append,List.count_append]
  omega

theorem Handoff.refl (w : World) : Handoff w w [] [] {} := by
  constructor <;> simp [HandoffDelta.items,HandoffDelta.owners]

theorem Handoff.trans (ha : Handoff w u a b x) (hb : Handoff u v b c y) :
    Handoff w v a c (x.append y) := by
  refine ⟨hb.base.trans ha.base,hb.rx.trans ha.rx,?_,?_,?_⟩
  · intro pid; rw [hb.tx,ha.tx]; simp [Option.map_map,Function.comp_def,List.append_assoc]
  · rw [hb.send,ha.send]; simp [HandoffDelta.append,Option.map_map,Function.comp_def,List.append_assoc]
  · intro o; have h := ha.count o; have j := hb.count o
    simp only [delta_append_owners_count]; omega

theorem base_of_peerView (h : peerView v = peerView w) : baseView v = baseView w := by
  apply Prod.ext
  · exact congrArg (fun x => x.1) h
  · funext pid
    have he := congrFun (congrArg Prod.snd h) pid
    simpa [baseView,peerView,Option.map_map,Function.comp_def] using
      congrArg (Option.map fun p => (p.1,p.2.2)) he

theorem handoff_of_view (h : protectView v = protectView w) : Handoff w v [] [] {} := by
  have hp := congrArg (fun x => x.1) h
  have hx := congrArg (fun x => x.2.1) h
  have ht := congrArg (fun x => x.2.2.1) h
  have hs := congrArg (fun x => x.2.2.2) h
  refine ⟨base_of_peerView hp,hx,?_,?_,?_⟩
  · intro pid; simpa [protectView] using congrFun ht pid
  · simpa [protectView] using hs
  · intro o; simpa using balance_view (o := o) hp

theorem queueOwners_base (hq : QueueOwners cs w) (he : baseView v = baseView w) : QueueOwners cs v := by
  intro d pid p id hd hp
  have epoch := congrArg Prod.fst he
  have own := congrFun (congrArg Prod.snd he) pid
  cases hw : w.k.wg with
  | none => simp [baseView,hw,hd] at epoch
  | some old =>
    have ep : d.ifindex = old.ifindex := by simpa [baseView,hw,hd] using epoch
    cases ho : old.peers[pid]? with
    | none => simp [baseView,hd,hp,hw,ho] at own
    | some op =>
      have fields : p.internalId = op.internalId ∧ p.rxQueue = op.rxQueue := by
        simpa [baseView,hd,hp,hw,ho] using own
      simpa [ep,fields.1,fields.2] using hq old pid op id hw ho

/-- The same input inventory, queue assignment and reservations survive a
closed handoff. The stronger conclusion also charges its actual durable delta. -/
theorem Handoff.protect (h : Handoff w v [] [] d) (hi : Inventory cs w)
    (hq : QueueOwners cs w) (hp : Protected cs loans w) :
    Inventory cs v ∧ QueueOwners cs v ∧ Protected cs loans v ∧
      Protected cs (loans ++ d.owners) v := by
  refine ⟨inventory_view hi h.rx,queueOwners_base hq h.base,?_,?_⟩
  · intro o; have old := hp o; have hc := h.count o
    simp only [List.count_nil,Nat.add_zero] at hc; omega
  · intro o; have old := hp o; have hc := h.count o
    simp only [List.count_nil,Nat.add_zero] at hc
    simp only [demand,List.count_append] at *; omega

/-- Supplied temporary loans are charged before and after the same transfer.
No reservation is inferred from unexplained reference-count slack. -/
theorem Handoff.funded (h : Handoff w v before after d) (hi : Inventory cs w)
    (hq : QueueOwners cs w) (hp : Protected cs (loans ++ before) w) :
    Inventory cs v ∧ QueueOwners cs v ∧ Protected cs (loans ++ after ++ d.owners) v := by
  refine ⟨inventory_view hi h.rx,queueOwners_base hq h.base,?_⟩
  intro o
  have old := hp o
  have hc := h.count o
  simp only [demand,List.count_append] at *
  omega

/-- A funded durable handoff has an actual resident owner at its endpoint. -/
theorem Handoff.durable_resident (h : Handoff w v before after d)
    (hp : Protected cs (loans ++ before) w) (ho : o ∈ d.owners) :
    ∃ p, resident v o = some p := by
  have old := hp o
  have hc := h.count o
  have pos : 0 < d.owners.count o := List.count_pos_iff.mpr ho
  simp only [demand,List.count_append] at old
  have hb : 0 < balance v o := by omega
  cases he : resident v o with
  | none => simp [balance,he] at hb
  | some p => exact ⟨p,rfl⟩

theorem protect_kernel (ha : SameKernel a) : SameView protectView a := by
  intro w x v hr
  unfold protectView peerView rxView handoffTxView sendView
  rw [ha w x v hr]

theorem modifyDev_protect (f : Device → Device)
    (he : ∀ d, (f d).ifindex = d.ifindex)
    (hp : ∀ d, (f d).peers = d.peers)
    (hr : ∀ d, (f d).rxSkbs = d.rxSkbs)
    (hs : ∀ d, (f d).sendWorkQueue = d.sendWorkQueue) : SameView protectView (modifyDev f) := by
  intro w x v h; cases h
  unfold protectView peerView rxView handoffTxView sendView
  simp [modifyDev,modifyK,
    Option.map_map,Option.bind_map,Function.comp_def,he,hp,hr,hs]

def protectCell (p : Peer) := (p.internalId,p.refcount,p.rxQueue,p.txQueue.all)
def protectPeerAt (w : World) (pid : PeerId) :=
  (w.k.wg.bind fun d => d.peers[pid]?).map protectCell

theorem protect_set_same (hd : w.k.wg = some d) (hp : d.peers[pid]? = some old)
    (hc : protectCell p = protectCell old) :
    protectView {w with k := {w.k with wg := some {d with peers := d.peers.insert pid p}}} = protectView w := by
  unfold protectView peerView rxView handoffTxView sendView
  simp only [hd,Option.map_some,Option.bind_some]
  have fields := Prod.mk.inj hc
  obtain ⟨hstamp,hcount,hrx,htx⟩ := (by simpa [protectCell] using hc :
    p.internalId = old.internalId ∧ p.refcount = old.refcount ∧ p.rxQueue = old.rxQueue ∧ p.txQueue.all = old.txQueue.all)
  refine Prod.ext (Prod.ext rfl ?_) (Prod.ext rfl (Prod.ext ?_ rfl))
  all_goals funext q; by_cases he : pid = q <;> simp_all [Std.TreeMap.getElem?_insert]

theorem getPeer_protect_spec (P : _ → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (protectView w)⌝⦄ getPeer pid
    ⦃⇓? p w => ⌜P (protectView w) ∧ protectPeerAt w pid = some (protectCell p)⌝⦄ := by
  mvcgen [getPeer,getDev,getK,invariant]
  all_goals simp_all [protectPeerAt]

theorem setPeer_protect_spec (P : _ → Prop) (pid : PeerId) (p : Peer) :
    ⦃fun w => ⌜P (protectView w) ∧ protectPeerAt w pid = some (protectCell p)⌝⦄ setPeer pid p
    ⦃⇓? _ w => ⌜P (protectView w)⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x v hi hr
  cases hd : w.k.wg with
  | none => simp [protectPeerAt,hd] at hi
  | some d =>
    obtain ⟨old,hp,hc⟩ := Option.map_eq_some_iff.mp (by simpa [protectPeerAt,hd] using hi.2)
    cases hr
    have he := protect_set_same (w := w) hd hp hc.symm
    simpa [setPeer,modifyDev,modifyK,hd,he] using hi.1

theorem modifyPeer_protect (pid : PeerId) (f : Peer → Peer)
    (hf : ∀ p, protectCell (f p) = protectCell p) : SameView protectView ((pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid f) := by
  change SameView protectView (do let p ← getPeer pid; setPeer pid (f p))
  apply SameView.of_wp
  intro s
  have hg := getPeer_protect_spec (fun t => t = s) pid
  have hs := fun p => setPeer_protect_spec (fun t => t = s) pid (f p)
  mvcgen [hg,hs]
  all_goals simpa [hf]

theorem getTx_protect (id : SkbId) : SameView protectView (getTxSkb id) :=
by
  apply SameView.of_wp
  intro s
  mvcgen [getTxSkb,getDev,getK,invariant]

theorem setTx_protect (id : SkbId) (f : DataPacket → DataPacket) : SameView protectView (setTxSkb id f) := by
  apply SameView.of_wp
  intro s
  have hg := (getTx_protect id).wp (fun t => t = s)
  have hm := fun p => (modifyDev_protect (fun d => {d with txSkbs := d.txSkbs.insert id (f p)})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)).wp (fun t => t = s)
  mvcgen [setTxSkb,hg,hm]

theorem keypairGet_protect (id : Option KeypairId) : SameView protectView (keypairGet id) := by
  apply SameView.of_wp
  intro s
  mvcgen [keypairGet,getKeypair,getDev,getK,setKeypair,modifyDev,modifyK,
    refcountIncNotZero,branch,branchCmp,branchCmpExcluded,invariant,unsupported]
  all_goals dsimp +zetaDelta only at *
  all_goals unfold protectView peerView rxView handoffTxView sendView at *
  all_goals simp_all

theorem keypairPut_protect (id : Option KeypairId) (now : Bool) : SameView protectView (keypairPut id now) := by
  apply SameView.of_wp
  intro s
  simp only [keypairPut,indexRemove_eq]
  have hd := fun o k => sameKernel_wp _ (indexOwner_peerDeref_sameKernel o) (fun v => v = k)
  mvcgen [hd,indexUnhash,getKeypair,getDev,getK,setKeypair,modifyDev,modifyK,
    refcountDecAndTest,branch,branchCmp,invariant,unsupported]
  all_goals dsimp +zetaDelta only at *
  all_goals unfold protectView peerView rxView handoffTxView sendView at *
  all_goals simp_all [Option.map_map,Option.bind_map,Function.comp_def]
  all_goals subst_vars
  all_goals simp_all

theorem acquire_handoff (hd : w.k.wg = some d) (hp : d.peers[pid]? = some p) :
    Handoff w {w with k := creditKernel w.k d pid p} [] [⟨d.ifindex,pid,p.internalId⟩] {} := by
  constructor
  · unfold baseView; simp [creditKernel,hd,Std.TreeMap.getElem?_insert,funext_iff]
    intro q; by_cases he : pid = q <;> simp_all
  · simp [rxView,creditKernel,hd]
  · intro q; unfold handoffTxView
    by_cases he : pid = q <;> simp_all [creditKernel,hd,Std.TreeMap.getElem?_insert,Function.comp_def]
  · simp [sendView,creditKernel,hd]
  · intro o; rw [credit_balance hd hp o]
    by_cases he : o = ⟨d.ifindex,pid,p.internalId⟩ <;> simp_all [List.count_cons,eq_comm]

theorem peerGet_handoff (hr : (peerGet pid).run w = .ok ((),v)) :
    ∃ d p, w.k.wg = some d ∧ d.peers[pid]? = some p ∧ 0 < p.refcount ∧
      Handoff w v [] [⟨d.ifindex,pid,p.internalId⟩] {} := by
  obtain ⟨d,p,hd,hp,pos,hv⟩ := peerGet_loan pid w v hr
  refine ⟨d,p,hd,hp,pos,?_⟩
  have he := acquire_handoff (w := w) hd hp
  constructor
  · simpa [baseView,creditKernel,hv] using he.base
  · simpa [rxView,creditKernel,hv] using he.rx
  · intro q; simpa [handoffTxView,creditKernel,hv] using he.tx q
  · simpa [sendView,creditKernel,hv] using he.send
  · intro o; simpa [balance,resident,creditKernel,hv] using he.count o

theorem Handoff.refl_loans (w : World) (loans : Reservations) : Handoff w w loans loans {} := by
  constructor <;> simp

theorem newTx_protect (pkt : DataPacket) : SameView protectView (newTxSkb pkt) := by
  apply SameView.of_wp
  intro s
  have hm := fun (d : Device) => (modifyDev_protect (fun v => {v with
    nextSkb := d.nextSkb + 1, txSkbs := v.txSkbs.insert d.nextSkb pkt})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)).wp (fun t => t=s)
  mvcgen [newTxSkb,getDev,getK,hm,invariant]

theorem freeTx_protect (id : SkbId) : SameView protectView (freeTxSkb id) := by
  apply SameView.of_wp
  intro s
  have hg := (getTx_protect id).wp (fun t => t=s)
  have hm := (modifyDev_protect (fun d => {d with txSkbs := d.txSkbs.erase id})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)).wp (fun t => t=s)
  mvcgen [freeTxSkb,hg,hm]

theorem cpu_protect (pid : PeerId) : SameView protectView (cpumaskChooseOnline pid) := by
  apply SameView.of_wp
  intro s
  have hg := getPeer_protect_spec (fun t => t=s) pid
  have hs := fun (p : Peer) => setPeer_protect_spec (fun t => t=s) pid {p with serialWorkCpu := some 0}
  simp only [cpumaskChooseOnline,Nat.mod_one]
  mvcgen [hg,hs,branch]
  all_goals try exact ((⇓? _ w => ⌜protectView w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals dsimp +zetaDelta only at *
  all_goals unfold protectView peerView rxView handoffTxView sendView at *
  all_goals simp_all [protectCell]

theorem peerPut_handoff (hd : w.k.wg = some d) (hp : d.peers[pid]? = some p)
    (hc : 1 < p.refcount) (hr : (peerPut (some pid)).run w = .ok ((),v)) :
    Handoff w v [⟨d.ifindex,pid,p.internalId⟩] [] {} := by
  have hk := (hoare_iff_triple _ _ _).mpr (peerPut_nonfinal_spec pid w.k d p hd hp hc) w () v rfl hr
  constructor
  · unfold baseView; rw [hk]; simp [hd,Std.TreeMap.getElem?_insert,funext_iff]
    intro q; by_cases he : pid=q <;> simp_all
  · simp [rxView,hk,hd]
  · intro q; unfold handoffTxView; rw [hk]
    by_cases he : pid=q <;> simp_all [hd,Std.TreeMap.getElem?_insert,Function.comp_def]
  · simp [sendView,hk,hd]
  · intro o
    have he := payment_balance (w:=w) hd hp (by omega) o
    have hn : p.refcount ≠ 1 := by omega
    have hv : balance v o = balance {w with k:=paymentKernel w.k d pid p} o := by
      simp [balance,resident,paymentKernel,hk,hn]
    rw [hv,he]
    by_cases ho : o = ⟨d.ifindex,pid,p.internalId⟩
    · subst o; simp [balance,resident,hd,hp]; omega
    · simp [ho,eq_comm]

theorem Handoff.after_view (h : Handoff w u before after d) (hv : protectView v = protectView u) :
    Handoff w v before after d := by
  have hf := handoff_of_view hv
  refine ⟨hf.base.trans h.base,hf.rx.trans h.rx,?_,?_,?_⟩
  · intro pid
    have he : handoffTxView v pid = handoffTxView u pid := by simpa using hf.tx pid
    exact he.trans (h.tx pid)
  · have he : sendView v = sendView u := by simpa using hf.send
    exact he.trans h.send
  · intro o
    have hc : balance v o = balance u o := by simpa using hf.count o
    rw [hc]; exact h.count o

theorem handoff_frame_spec (ha : SameView protectView a) (w : World)
    (before after : Reservations) (d : HandoffDelta) :
    ⦃fun u => ⌜Handoff w u before after d⌝⦄ a
    ⦃⇓? _ v => ⌜Handoff w v before after d⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro u x v h hr
  exact h.after_view (ha u x v hr)

theorem protectPeerAt_view (he : protectView v = protectView w) (pid : PeerId) :
    protectPeerAt v pid = protectPeerAt w pid := by
  have hp := congrFun (congrArg (fun x => x.1.2) he) pid
  have ht := congrFun (congrArg (fun x => x.2.2.1) he) pid
  simp only [protectPeerAt,protectCell,protectView,peerView,handoffTxView] at *
  cases hv : (v.k.wg.bind fun d => d.peers[pid]?) <;>
    cases hw : (w.k.wg.bind fun d => d.peers[pid]?) <;> simp_all [protectCell]

/-- Repay the actual attributed temporary loan. Its positive pre-acquisition
balance prevents final retirement; no global residency assumption is supplied. -/
theorem repay_handoff (h : Handoff w u [] [o] {}) (pos : 0 < balance w o)
    (hr : (peerPut (some o.slot)).run u = .ok ((),v)) : Handoff w v [] [] {} := by
  have hc := h.count o
  simp only [List.count_cons_self,List.count_nil,delta_empty_owners,Nat.add_zero] at hc
  have hu : 1 < balance u o := by omega
  cases hp : resident u o with
  | none => simp [balance,hp] at hu
  | some p =>
    obtain ⟨d,hd,he,hs,ht⟩ := resident_fields hp
    have count : 1 < p.refcount := by simpa [balance,hp] using hu
    have ho : o = ⟨d.ifindex,o.slot,p.internalId⟩ := by cases o; simp_all
    have paid := peerPut_handoff hd hs count hr
    rw [← ho] at paid
    simpa [HandoffDelta.append] using h.trans paid

end Leanux.Proofs.WG.Queues.RxCredits
