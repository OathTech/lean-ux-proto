import Leanux.Proofs.WG.Queues.RxCarrierState
import Leanux.Proofs.Framing.Index

/-! Actual RX peer-credit payment and the selected/paid/free boundary. A failed
call has an access prefix, not a returned World. A paid RX cell remains in the
store until free and no longer contributes a peer credit. -/
namespace Leanux.Proofs.WG.Queues.RxCredits
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
set_option pp.structureInstances false

def paymentKernel (k : Kernel) (d : Device) (pid : PeerId) (p : Peer) : Kernel :=
  {k with wg := some ({d with peers := (if p.refcount = 1 then d.peers.erase pid
    else d.peers.insert pid {p with refcount := p.refcount - 1})})}

/-- Projection of the original successful payment, including final release. -/
theorem peerPut_effect (pid : PeerId) (w v : World) (d : Device) (p : Peer)
    (hd : w.k.wg = some d) (hp : d.peers[pid]? = some p)
    (hr : (peerPut (some pid)).run w = .ok ((),v)) :
    0 < p.refcount ∧
    peerView v = peerView {w with k := paymentKernel w.k d pid p} ∧ rxView v = rxView w := by
  have hg := PeerBorrow.getPeer_known w.k d pid p hd hp
  have hs : ⦃fun z => ⌜z.k = w.k⌝⦄ peerPut (some pid)
      ⦃⇓? _ z => ⌜0 < p.refcount ∧
        peerView z = peerView {w with k := paymentKernel w.k d pid p} ∧ rxView z = rxView w⌝⦄ := by
    simp only [peerPut,indexRemove_eq]
    mvcgen [hg,requireNotPending,getDev,getK,setPeer,modifyDev,modifyK,refcountDecAndTest,
      branch,branchCmp,indexUnhash,retirePeerUnits,invariant,unsupported]
    all_goals dsimp +zetaDelta only at *
    all_goals simp_all [peerView,rxView,paymentKernel]
    all_goals try omega
    all_goals subst_vars
    all_goals dsimp only
    all_goals simp [funext_iff,Std.TreeMap.getElem?_insert,Std.TreeMap.getElem?_erase]
    all_goals intro q; by_cases h : pid = q <;> simp [h]
  exact (hoare_iff_triple _ _ _).mpr hs w () v rfl hr

/-- Positive credit makes the original payment total. Zero-count writes before
failure remain covered by the existing access observer, outside this premise. -/
theorem peerPut_returns (pid : PeerId) (w : World) (d : Device) (p : Peer)
    (hd : w.k.wg = some d) (hp : d.peers[pid]? = some p) (hc : 0 < p.refcount) :
    ∃ v, (peerPut (some pid)).run w = .ok ((),v) := by
  have hz : p.refcount ≠ 0 := by omega
  have hn : ¬ p.refcount < 1 := by omega
  by_cases he : p.refcount = 1
  all_goals simp [peerPut,requireNotPending,getPeer,getDev,getK,hd,hp,setPeer,modifyDev,modifyK,
    refcountDecAndTest,branch,branchCmp,hc,hz,hn,he,indexRemove_eq,indexUnhash,retirePeerUnits]

def viewBalance (v : Option Nat × (PeerId → Option (Nat × Nat × PrevQueue SkbId))) (o : Owner) : Nat :=
  if v.1 = some o.epoch then match v.2 o.slot with
    | none => 0
    | some (stamp,count,_) => if stamp = o.stamp then count else 0
  else 0

theorem balance_factor (w : World) (o : Owner) : balance w o = viewBalance (peerView w) o := by
  cases hd : w.k.wg with
  | none => simp [balance,resident,peerView,viewBalance,hd]
  | some d =>
    cases hp : d.peers[o.slot]? <;>
      simp [balance,resident,peerView,viewBalance,hd,hp]
    repeat' first | split | (simp_all; done)

theorem balance_view (he : peerView v = peerView w) : balance v o = balance w o := by
  rw [balance_factor,balance_factor,he]

theorem payment_balance (hd : w.k.wg = some d) (hp : d.peers[pid]? = some p)
    (hc : 0 < p.refcount) (o : Owner) :
    balance {w with k := paymentKernel w.k d pid p} o =
      if o = ⟨d.ifindex,pid,p.internalId⟩ then balance w o - 1 else balance w o := by
  rcases o with ⟨epoch,slot,stamp⟩
  simp only [balance_factor,peerView,viewBalance,paymentKernel,hd,Option.map_some,Option.bind_some]
  by_cases he : d.ifindex = epoch <;> by_cases hi : pid = slot <;>
    by_cases hs : p.internalId = stamp <;> by_cases hn : p.refcount = 1
  all_goals simp_all [Std.TreeMap.getElem?_insert,Std.TreeMap.getElem?_erase,Owner.mk.injEq]
  all_goals first | (intro h; exact False.elim (hi h.symm)) | omega

/-- Payment consumes the selected carrier's attributed credit. Other unpaid
carriers and explicit reservations remain backed, even when the paid peer retires. -/
theorem selected_payment (hi : Protected (c :: cs) loans w) (hc : c.phase = .selected) :
    ∃ v, (peerPut (some c.owner.slot)).run w = .ok ((),v) ∧
      Protected (paid c :: cs) loans v ∧ rxView v = rxView w ∧
      (0 < demand cs loans c.owner → ∃ p, resident v c.owner = some p) := by
  obtain ⟨p,hp,hb⟩ := selected_credit hi hc
  obtain ⟨d,hd,he,hs,ht⟩ := resident_fields hp
  have pos : 0 < p.refcount := by omega
  obtain ⟨v,hv⟩ := peerPut_returns c.owner.slot w d p hd hs pos
  obtain ⟨_,hview,hrx⟩ := peerPut_effect _ w v d p hd hs hv
  have own : c.owner = ⟨d.ifindex,c.owner.slot,p.internalId⟩ := by
    simp only [he,ht]
  have safe : Protected (paid c :: cs) loans v := by
    intro o
    have old := hi o
    have eq := (balance_view (o := o) hview).trans (payment_balance hd hs pos o)
    by_cases ho : o = c.owner
    · subst o
      rw [← own,if_pos rfl] at eq
      simp only [demand,charges_paid] at *
      have count : charges (c :: cs) c.owner = 1 + charges cs c.owner := by
        simp [hc,Phase.charged]
      rw [count] at old
      omega
    · have ne : o ≠ ⟨d.ifindex,c.owner.slot,p.internalId⟩ := by simpa only [← own] using ho
      rw [if_neg ne] at eq
      simp only [demand,charges_paid] at *
      have count : charges (c :: cs) o = charges cs o := by simp [Ne.symm ho]
      rw [count] at old
      simpa only [eq] using old
  refine ⟨v,hv,safe,hrx,?_⟩
  intro remaining
  obtain ⟨p,hp,_⟩ := protected_resident safe (o := c.owner) (by simpa only [demand,charges_paid] using remaining)
  exact ⟨p,hp⟩

/-- Keypair cleanup never pays a peer reference or changes an RX store cell. -/
theorem keypairPut_credit_frame (kid : Option KeypairId) (now : Bool) :
    SameView (fun w => (peerView w,rxView w)) (keypairPut kid now) := by
  apply SameView.of_wp
  intro s
  simp only [keypairPut,indexRemove_eq]
  have deref := fun owner k => sameKernel_wp _ (indexOwner_peerDeref_sameKernel owner) (fun v => v = k)
  mvcgen [deref,indexUnhash,getKeypair,getDev,getK,setKeypair,modifyDev,modifyK,
    refcountDecAndTest,branch,branchCmp,invariant,unsupported]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [peerView,rxView]
  all_goals subst_vars
  all_goals simp_all [peerView,rxView]

theorem protected_view (hi : Protected cs loans w) (he : peerView v = peerView w) :
    Protected cs loans v := by
  intro o
  simpa only [balance_view (o := o) he] using hi o

theorem packetAt_view (he : rxView v = rxView w) : packetAt v p = packetAt w p := by
  have h := Prod.mk.inj he
  cases hv : v.k.wg <;> cases hw : w.k.wg <;>
    simp_all [rxView,packetAt]

theorem inventory_view (hi : Inventory cs w) (he : rxView v = rxView w) :
    Inventory cs v := by
  refine ⟨hi.distinct,?_,?_⟩
  · intro c hc
    obtain ⟨hep,p,hp,ho⟩ := hi.present c hc
    exact ⟨hep,p,(packetAt_view he).trans hp,ho⟩
  · intro d id p hd hp
    have hepoch := (Prod.mk.inj he).1
    have hslot := congrFun (Prod.mk.inj he).2 id
    cases hw : w.k.wg with
    | none => simp [rxView,hd,hw] at hepoch
    | some old =>
      have epoch : d.ifindex = old.ifindex := by simpa [rxView,hd,hw] using hepoch
      have slot : old.rxSkbs[id]? = some p := by simpa [rxView,hd,hw,hp] using hslot.symm
      obtain ⟨c,hc,he⟩ := hi.complete old id p hw slot
      exact ⟨c,hc,by simpa [epoch] using he⟩

theorem inventory_paid (hi : Inventory (c :: cs) w) : Inventory (paid c :: cs) w := by
  refine ⟨by simpa [paid] using hi.distinct,?_,?_⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · simpa [paid] using hi.present c (by simp)
    · exact hi.present x (by simp [hx])
  · intro d id p hd hp
    obtain ⟨x,hx,he⟩ := hi.complete d id p hd hp
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨paid x,by simp,by simpa [paid] using he⟩
    · exact ⟨x,by simp [hx],he⟩

/-- The paid cell is really present, so original free returns normally. It
removes that allocation and keeps all other packet identities and peer credits. -/
theorem paid_free (hi : Inventory (paid c :: cs) w)
    (hs : Protected (paid c :: cs) loans w) :
    ∃ v, (freeRxSkb c.packet.slot).run w = .ok ((),v) ∧
      Inventory cs v ∧ Protected cs loans v ∧ packetAt v c.packet = none := by
  obtain ⟨hep,p,hp,ho⟩ := hi.present (paid c) (by simp)
  change packetAt w c.packet = some p at hp
  cases hd : w.k.wg with
  | none => simp [packetAt,hd] at hp
  | some d =>
    have epoch : d.ifindex = c.packet.epoch := by
      by_cases hn : d.ifindex = c.packet.epoch
      · exact hn
      · simp [packetAt,hd,hn] at hp
    have slot : d.rxSkbs[c.packet.slot]? = some p := by simpa [packetAt,hd,epoch] using hp
    let v := Packets.update w fun d => {d with rxSkbs := d.rxSkbs.erase c.packet.slot}
    have view : peerView v = peerView w := by simp [v,peerView,Packets.update,hd]
    have different : ∀ x ∈ cs, x.packet ≠ c.packet := by
      intro x hx he
      have h := (List.nodup_cons.mp hi.distinct).1
      exact h (List.mem_map.mpr ⟨x,hx,by simpa [paid] using he⟩)
    have keeps : ∀ x ∈ cs, packetAt v x.packet = packetAt w x.packet := by
      intro x hx
      have ep := (hi.present x (by simp [hx])).1
      obtain ⟨q,hq,_⟩ := (hi.present x (by simp [hx])).2
      have xe : d.ifindex = x.packet.epoch := by
        by_cases hn : d.ifindex = x.packet.epoch
        · exact hn
        · simp [packetAt,hd,hn] at hq
      have ne : c.packet.slot ≠ x.packet.slot := by
        intro he
        apply different x hx
        cases hxp : x.packet
        cases hcp : c.packet
        simp_all [Packet.mk.injEq]
      simp [v,packetAt,Packets.update,hd,xe,Std.TreeMap.getElem?_erase,ne]
    refine ⟨v,Packets.freeRxSkb_run w d _ p hd slot,?_,?_,?_⟩
    · refine ⟨(List.nodup_cons.mp hi.distinct).2,?_,?_⟩
      · intro x hx
        obtain ⟨ep,q,hq,ho⟩ := hi.present x (by simp [hx])
        exact ⟨ep,q,(keeps x hx).trans hq,ho⟩
      · intro out id q hout hq
        have outEq : out = {d with rxSkbs := d.rxSkbs.erase c.packet.slot} := by
          simpa [v,Packets.update,hd] using hout.symm
        subst out
        have ne : c.packet.slot ≠ id := by
          intro he
          simp [← he] at hq
        have old : d.rxSkbs[id]? = some q := by simpa [Std.TreeMap.getElem?_erase,ne] using hq
        obtain ⟨x,hx,he⟩ := hi.complete d id q hd old
        rcases List.mem_cons.mp hx with rfl | hx
        · have bad : c.packet.slot = id := congrArg Packet.slot he
          exact False.elim (ne bad)
        · exact ⟨x,hx,he⟩
    · apply protected_view (w := w) _ view
      simpa only [Protected,demand,charges_paid] using hs
    · simp [v,packetAt,Packets.update,hd,epoch]

/-- The literal poll cleanup cut, without a fabricated World for a Stop. -/
def cleanup (id : SkbId) (pkt : RxPacket) (releaseFlag : Bool) : M Unit := do
  keypairPut (some pkt.keypair) false
  peerPut (some pkt.peer)
  _ ← branch .rxPollFree releaseFlag
  freeRxSkb id

/-- Once the original key payment has returned, the attributed selected peer
credit makes the remaining literal cleanup total, including final retirement. -/
theorem cleanup_discharge (hi : Inventory (c :: cs) w)
    (hs : Protected (c :: cs) loans w) (phase : c.phase = .selected)
    (hp : packetAt w c.packet = some pkt) (owner : pkt.peer = c.owner.slot)
    (hk : (keypairPut (some pkt.keypair) false).run w = .ok ((),a)) :
    ∃ v, (cleanup c.packet.slot pkt flag).run w = .ok ((),v) ∧
      Inventory cs v ∧ Protected cs loans v ∧ packetAt v c.packet = none := by
  have hv := Prod.mk.inj (keypairPut_credit_frame (some pkt.keypair) false w () a hk)
  have ia := inventory_view hi hv.2
  have sa := protected_view hs hv.1
  obtain ⟨b,hb,sb,rb,_⟩ := selected_payment sa phase
  have ib := inventory_paid (inventory_view ia rb)
  let z := {b with steps := b.steps.push {decision := .rxPollFree, outcome := flag, netRx := b.netRxSection}}
  have hz : (branch .rxPollFree flag).run b = .ok (flag,z) := by rfl
  have iz : Inventory (paid c :: cs) z := inventory_view ib rfl
  have sz : Protected (paid c :: cs) loans z := protected_view sb rfl
  obtain ⟨v,hf,iv,sv,pv⟩ := paid_free iz sz
  refine ⟨v,?_,iv,sv,pv⟩
  simp only [cleanup,MaterialOrigin.bind_ok]
  exact ⟨(),a,hk,(),b,by simpa [owner] using hb,flag,z,hz,hf⟩

/-- The original poll uses its caller pid; the earlier source guard is the
explicit equality identifying that pid with this packet's peer. -/
theorem cleanup_poll_guard (id : SkbId) (pkt : RxPacket) (pid : PeerId) (flag : Bool)
    (guard : pkt.peer = pid) : cleanup id pkt flag = (do
      keypairPut (some pkt.keypair) false
      peerPut (some pid)
      _ ← branch .rxPollFree flag
      freeRxSkb id) := by simp only [cleanup,guard]

theorem queueOwners_view (hi : QueueOwners cs w) (he : peerView v = peerView w) :
    QueueOwners cs v := by
  intro d pid p id hd hp
  have epoch := (Prod.mk.inj he).1
  have slot := congrFun (Prod.mk.inj he).2 pid
  cases hw : w.k.wg with
  | none => simp [peerView,hd,hw] at epoch
  | some old =>
    have ep : d.ifindex = old.ifindex := by simpa [peerView,hd,hw] using epoch
    cases hq : old.peers[pid]? with
    | none => simp [peerView,hd,hp,hw,hq] at slot
    | some q =>
      have fields : p.internalId = q.internalId ∧ p.refcount = q.refcount ∧ p.rxQueue = q.rxQueue := by
        simpa [peerView,hd,hp,hw,hq] using slot
      simpa [ep,fields.1,fields.2.2] using hi old pid q id hw hq

theorem queueOwners_paid (hi : QueueOwners (c :: cs) w) (hc : c.phase = .selected) :
    QueueOwners (paid c :: cs) w := by
  intro d pid p id hd hp
  simpa [List.filter_cons,paid,hc] using hi d pid p id hd hp

theorem queueOwners_paid_iff : QueueOwners (paid c :: cs) w ↔ QueueOwners cs w := by
  simp [QueueOwners,paid,List.filter_cons]

theorem freeRxSkb_peerView (id : SkbId) : SameView peerView (freeRxSkb id) := by
  apply SameView.of_wp
  intro s
  mvcgen [freeRxSkb,getRxSkb,getDev,getK,modifyDev,modifyK,invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [peerView]

/-- Removing a peer drops its queue obligation; a nonfinal payment preserves
its queue and identity. This is the actual payment projection, not retention. -/
theorem queueOwners_paymentKernel (hi : QueueOwners cs w)
    (hd : w.k.wg = some d) (hp : d.peers[pid]? = some p) :
    QueueOwners cs {w with k := paymentKernel w.k d pid p} := by
  intro out qid q id hout hq
  have he : out = {d with peers := (if p.refcount = 1 then d.peers.erase pid else d.peers.insert pid {p with refcount := p.refcount - 1})} := by
    simpa [paymentKernel] using hout.symm
  subst out
  by_cases hc : p.refcount = 1
  · by_cases hpid : pid = qid
    · simp [hc,Std.TreeMap.getElem?_erase,hpid] at hq
    · have old : d.peers[qid]? = some q := by simpa [hc,Std.TreeMap.getElem?_erase,hpid] using hq
      exact hi d qid q id hd old
  · by_cases hpid : pid = qid
    · subst qid
      have eq : q = {p with refcount := p.refcount - 1} := by simpa [hc] using hq.symm
      subst q
      exact hi d pid p id hd hp
    · have old : d.peers[qid]? = some q := by simpa [hc,Std.TreeMap.getElem?_insert,hpid] using hq
      exact hi d qid q id hd old

/-- The same queue ownership ledger survives selected credit payment. -/
theorem selected_payment_queues (hq : QueueOwners (c :: cs) w)
    (hc : c.phase = .selected) (hd : w.k.wg = some d) (hp : d.peers[c.owner.slot]? = some p)
    (hr : (peerPut (some c.owner.slot)).run w = .ok ((),v)) :
    QueueOwners (paid c :: cs) v := by
  exact queueOwners_paid
    (queueOwners_view (queueOwners_paymentKernel hq hd hp)
      (peerPut_effect _ w v d p hd hp hr).2.1) hc

/-- Free preserves the same remaining queue ownership; a paid cell contributes
no queued occurrence, so no remaining item is silently removed from this ledger. -/
theorem paid_free_queues (hi : QueueOwners (paid c :: cs) w)
    (hr : (freeRxSkb c.packet.slot).run w = .ok ((),v)) : QueueOwners cs v :=
  queueOwners_view (queueOwners_paid_iff.mp hi) (freeRxSkb_peerView _ w () v hr)

def selected (c : Carrier) : Carrier := {c with phase := .selected}

theorem inventory_selected (hi : Inventory (c :: cs) w) : Inventory (selected c :: cs) w := by
  refine ⟨by simpa [selected] using hi.distinct,?_,?_⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · simpa [selected] using hi.present c (by simp)
    · exact hi.present x (by simp [hx])
  · intro d id p hd hp
    obtain ⟨x,hx,he⟩ := hi.complete d id p hd hp
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨selected x,by simp,by simpa [selected] using he⟩
    · exact ⟨x,by simp [hx],he⟩

theorem selected_protected (hi : Protected (c :: cs) loans w) (hc : c.phase.charged = true) :
    Protected (selected c :: cs) loans w := by
  intro o
  have h : charges (selected c :: cs) o = charges (c :: cs) o := by
    cases phase : c.phase <;> simp_all [selected,Phase.charged]
  simpa only [demand,h] using hi o

/-- The cached head stays queued until the actual drop. This source cut changes
exactly that cell's phase and removes one queue occurrence, keeping the same
remaining inventory and attributed reservations. -/
theorem drop_selection (id : SkbId) (hd : w.k.wg = some d) (hp : d.peers[pid]? = some p)
    (peek : p.rxQueue.peeked = some id)
    (hi : Inventory (⟨⟨d.ifindex,id⟩,⟨d.ifindex,pid,p.internalId⟩,.queued⟩ :: cs) w)
    (hq : QueueOwners (⟨⟨d.ifindex,id⟩,⟨d.ifindex,pid,p.internalId⟩,.queued⟩ :: cs) w)
    (hs : Protected (⟨⟨d.ifindex,id⟩,⟨d.ifindex,pid,p.internalId⟩,.queued⟩ :: cs) loans w) :
    ∃ v, (dropRxQueue pid).run w = .ok ((),v) ∧
      Inventory (⟨⟨d.ifindex,id⟩,⟨d.ifindex,pid,p.internalId⟩,.selected⟩ :: cs) v ∧
      QueueOwners (⟨⟨d.ifindex,id⟩,⟨d.ifindex,pid,p.internalId⟩,.selected⟩ :: cs) v ∧
      Protected (⟨⟨d.ifindex,id⟩,⟨d.ifindex,pid,p.internalId⟩,.selected⟩ :: cs) loans v := by
  let out : Peer := {p with rxQueue := p.rxQueue.dropPeeked}
  let v := Packets.update w fun d => {d with peers := d.peers.insert pid out}
  have hr : (dropRxQueue pid).run w = .ok ((),v) := by
    simp [dropRxQueue,getPeer,getDev,getK,setPeer,modifyDev,modifyK,hd,hp,v,Packets.update,out]
  have rx : rxView v = rxView w := by simp [rxView,v,Packets.update,hd]
  have bal : ∀ o, balance v o = balance w o := by
    intro o
    simp only [balance_factor,peerView,viewBalance,v,Packets.update,hd,Option.map_some,Option.bind_some]
    by_cases hpid : pid = o.slot <;> simp [Std.TreeMap.getElem?_insert,hpid,out]
    simp [← hpid,hp]
  refine ⟨v,hr,inventory_view (inventory_selected hi) rx,?_,?_⟩
  · intro dev qid q sid hdev hqslot
    have he : dev = {d with peers := d.peers.insert pid out} := by
      simpa [v,Packets.update,hd] using hdev.symm
    subst dev
    by_cases same : pid = qid
    · subst qid
      have eq : q = out := by simpa using hqslot.symm
      subst q
      have old := hq d pid p sid hd hp
      simp only [List.filter_cons] at old ⊢
      simp [out,PrevQueue.all,PrevQueue.dropPeeked,peek] at old ⊢
      by_cases hid : id = sid <;> simp_all [Packet.mk.injEq,Owner.mk.injEq]
      all_goals omega
    · have oldq : d.peers[qid]? = some q := by simpa [Std.TreeMap.getElem?_insert,same] using hqslot
      have old := hq d qid q sid hd oldq
      simpa [List.filter_cons,Owner.mk.injEq,same] using old
  · intro o
    rw [bal]
    exact selected_protected hs rfl o

/-- Source ENOSPC cleanup has no poll-free decision: key put, peer put, free. -/
def discard (id : SkbId) (pkt : RxPacket) : M Unit := do
  keypairPut (some pkt.keypair) false
  peerPut (some pkt.peer)
  freeRxSkb id

/-- A successful original key payment discharges an unpublished packet's own
peer loan, then frees the actual resident cell. The same remaining ledgers,
including queue multiplicities, survive; the paid phase is not reselected. -/
theorem discard_unpublished (hi : Inventory (c :: cs) w)
    (hs : Protected (c :: cs) loans w) (hq : QueueOwners (c :: cs) w)
    (phase : c.phase = .unpublished) (owner : pkt.peer = c.owner.slot)
    (hk : (keypairPut (some pkt.keypair) false).run w = .ok ((),a)) :
    ∃ v, (discard c.packet.slot pkt).run w = .ok ((),v) ∧
      Inventory cs v ∧ Protected cs loans v ∧ QueueOwners cs v ∧ packetAt v c.packet = none := by
  have hv := Prod.mk.inj (keypairPut_credit_frame (some pkt.keypair) false w () a hk)
  have ia := inventory_selected (inventory_view hi hv.2)
  have sa := selected_protected (protected_view hs hv.1) (by simp [phase,Phase.charged])
  have qa : QueueOwners (selected c :: cs) a := by
    have q := queueOwners_view hq hv.1
    intro d pid p id hd hp
    simpa [List.filter_cons,selected,phase] using q d pid p id hd hp
  obtain ⟨p,hp,_⟩ := selected_credit sa rfl
  obtain ⟨d,hd,_,hdp,_⟩ := resident_fields hp
  obtain ⟨b,hb,sb,rb,_⟩ := selected_payment sa rfl
  have ib := inventory_paid (inventory_view ia rb)
  have qb := selected_payment_queues qa rfl hd hdp hb
  obtain ⟨v,hf,iv,sv,pv⟩ := paid_free ib sb
  refine ⟨v,?_,iv,sv,paid_free_queues qb hf,pv⟩
  simp only [discard,MaterialOrigin.bind_ok]
  exact ⟨(),a,hk,(),b,by simpa [selected,owner] using hb,hf⟩

/-- A key-payment Stop is retained by both literal cleanup cuts, with no
invented paid/free endpoint or failed World. -/
theorem cleanup_key_stop (id : SkbId) (hk : (keypairPut (some pkt.keypair) false).run w = .error reason) :
    (cleanup id pkt flag).run w = .error reason ∧
      (discard id pkt).run w = .error reason := by
  simp [cleanup,discard,StateT.run_bind,hk]

end Leanux.Proofs.WG.Queues.RxCredits
