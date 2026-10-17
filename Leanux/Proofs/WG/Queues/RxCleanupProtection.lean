import Leanux.Proofs.WG.Queues.RxCarrierState
import Leanux.Proofs.Framing.Index
import Leanux.Proofs.WG.Origins.RetainingLeaves

/-! Actual RX peer-credit payment and the selected/paid/free boundary. A failed
call has an access prefix, not a returned WGWorld. A paid RX cell remains in the
store until free and no longer contributes a peer credit. -/
namespace Leanux.Proofs.WG.Queues.RxCredits
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
set_option pp.structureInstances false

/-- A pure update used only under the peer-credit and packet observations.
It does not model a separate execution state or assert the release's other effects. -/
def paymentState (w : WGWorld) (d : Device) (pid : PeerId) (p : Peer) : WGWorld :=
  {w with dev := some {d with peers := (if p.refcount = 1 then d.peers.erase pid
    else d.peers.insert pid {p with refcount := p.refcount - 1})}}

/-- Projection of the original successful payment, including final release. -/
theorem peerPut_effect (pid : PeerId) (w v : WGWorld) (d : Device) (p : Peer)
    (ambient ambient' : Ambient)
    (hd : w.dev = some d) (hp : d.peers[pid]? = some p)
    (hr : ((peerPut (some pid)).run w).run ambient = .ok (((),v),ambient')) :
    0 < p.refcount ∧
    peerView v = peerView (paymentState w d pid p) ∧ rxView v = rxView w := by
  have hl (a : IndexM Unit) : (liftM a : WG.M Unit) = liftIndex a := rfl
  by_cases positive : 0 < p.refcount
  · refine ⟨positive, ?_⟩
    have nonzero : p.refcount ≠ 0 := by omega
    have nonnegative : ¬ p.refcount < 1 := by omega
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
    all_goals
      simp_all [peerView, rxView, paymentState, and_assoc,
        Std.TreeMap.getElem?_insert, Std.TreeMap.getElem?_erase]
    all_goals intro q; by_cases h : pid = q <;> simp [h]
  · have zero : p.refcount = 0 := by omega
    simp [peerPut, requireNotPending, getPeer, getDev, setPeer, modifyDev,
      refcountDecAndTest, branch, branchCmp, CounterWindow.branch_run,
      CounterWindow.branchCmp_run, hd, hp, zero,
      StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
      CounterWindow.except_ok_bind, CounterWindow.except_pure,
      unsupported, AmbientM.unsupported] at hr
    cases hr

/-- A nonfinal payment returns normally. This is distinct from the withdrawn
positive-credit totality claim: final release has queue and timer guards. -/
theorem peerPut_nonfinal_returns (pid : PeerId) (w : WGWorld) (d : Device) (p : Peer)
    (ambient : Ambient)
    (hd : w.dev = some d) (hp : d.peers[pid]? = some p) (hc : 1 < p.refcount) :
    ∃ v ambient', ((peerPut (some pid)).run w).run ambient = .ok (((),v),ambient') := by
  have positive : 0 < p.refcount := by omega
  have nonzero : p.refcount ≠ 0 := by omega
  have nonnegative : ¬ p.refcount < 1 := by omega
  have nonfinal : p.refcount ≠ 1 := by omega
  simp [peerPut, requireNotPending, getPeer, getDev, setPeer, modifyDev,
    refcountDecAndTest, branch, branchCmp, CounterWindow.branch_run,
    CounterWindow.branchCmp_run, hd, hp, positive, nonzero, nonfinal,
    StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
    CounterWindow.except_ok_bind, CounterWindow.except_pure]

def viewBalance (v : Option Nat × (PeerId → Option (Nat × Nat × PrevQueue SkbId))) (o : Owner) : Nat :=
  if v.1 = some o.epoch then match v.2 o.slot with
    | none => 0
    | some (stamp,count,_) => if stamp = o.stamp then count else 0
  else 0

theorem balance_factor (w : WGWorld) (o : Owner) : balance w o = viewBalance (peerView w) o := by
  cases hd : w.dev with
  | none => simp [balance,resident,peerView,viewBalance,hd]
  | some d =>
    cases hp : d.peers[o.slot]? <;>
      simp [balance,resident,peerView,viewBalance,hd,hp]
    repeat' first | split | (simp_all; done)

theorem balance_view (he : peerView v = peerView w) : balance v o = balance w o := by
  rw [balance_factor,balance_factor,he]

theorem payment_balance (hd : w.dev = some d) (hp : d.peers[pid]? = some p)
    (hc : 0 < p.refcount) (o : Owner) :
    balance (paymentState w d pid p) o =
      if o = ⟨d.ifindex,pid,p.internalId⟩ then balance w o - 1 else balance w o := by
  rcases o with ⟨epoch,slot,stamp⟩
  simp only [balance_factor,peerView,viewBalance,paymentState,hd,Option.map_some,Option.bind_some]
  by_cases he : d.ifindex = epoch <;> by_cases hi : pid = slot <;>
    by_cases hs : p.internalId = stamp <;> by_cases hn : p.refcount = 1
  all_goals simp_all [Std.TreeMap.getElem?_insert,Std.TreeMap.getElem?_erase,Owner.mk.injEq]
  all_goals first | (intro h; exact False.elim (hi h.symm)) | omega

/-- Payment consumes the selected carrier's attributed credit. On an actual normal return, other unpaid
carriers and explicit reservations remain backed, even when the paid peer retires. -/
theorem selected_payment_normal (hi : Protected (c :: cs) loans w) (hc : c.phase = .selected)
    (ambient ambient' : Ambient)
    (hr : ((peerPut (some c.owner.slot)).run w).run ambient = .ok (((),v),ambient')) :
    Protected (paid c :: cs) loans v ∧ rxView v = rxView w ∧
      (0 < demand cs loans c.owner → ∃ p, resident v c.owner = some p) := by
  obtain ⟨p,hp,hb⟩ := selected_credit hi hc
  obtain ⟨d,hd,he,hs,ht⟩ := resident_fields hp
  have pos : 0 < p.refcount := by omega
  obtain ⟨_,hview,hrx⟩ := peerPut_effect _ w v d p ambient ambient' hd hs hr
  have own : c.owner = ⟨d.ifindex,c.owner.slot,p.internalId⟩ := by
    simp only [he,ht]
  have safe : Protected (paid c :: cs) loans v := by
    intro o
    have old := hi o
    have eq := (balance_view (o := o) hview).trans (payment_balance hd hs pos o)
    by_cases ho : o = c.owner
    · subst o
      rw [← own,ite_eq_left rfl] at eq
      simp only [demand,charges_paid] at *
      have count : charges (c :: cs) c.owner = 1 + charges cs c.owner := by
        simp [hc,Phase.charged]
      rw [count] at old
      omega
    · have ne : o ≠ ⟨d.ifindex,c.owner.slot,p.internalId⟩ := by simpa only [← own] using ho
      rw [ite_eq_right ne] at eq
      simp only [demand,charges_paid] at *
      have count : charges (c :: cs) o = charges cs o := by simp [Ne.symm ho]
      rw [count] at old
      simpa only [eq] using old
  refine ⟨safe,hrx,?_⟩
  intro remaining
  obtain ⟨p,hp,_⟩ := protected_resident safe (o := c.owner) (by simpa only [demand,charges_paid] using remaining)
  exact ⟨p,hp⟩

open Lean Meta Elab Tactic

elab "credit_component " indexRule:term : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  let args := target.getAppArgs
  unless (target.isAppOf ``Hoare || target.isAppOf ``Triple) && args.size ≥ 3 do
    throwError "not an endpoint contract"
  let action := args[args.size-3]!.consumeMData
  let .const name _ := action.getAppFn | throwError "not a component lift"
  unless [``monadLift,``MonadLift.monadLift,``MonadLiftT.monadLift,``StateT.lift,``liftIndex].contains name do
    throwError "not a component lift"
  let actionArgs := action.getAppArgs
  unless actionArgs.size > 0 do throwError "missing component action"
  let source := actionArgs.back!
  let saved ← saveState
  try
    let proof ← mkAppM ``hoare_liftAmbient #[source,args[args.size-2]!]
    replaceMainGoal (← goal.apply proof)
  catch _ =>
    saved.restore
    let rule ← Term.elabTerm indexRule none
    let proof ← mkAppM' rule #[source]
    replaceMainGoal (← goal.apply proof)

/-- Keypair cleanup never pays a peer reference or changes an RX store cell. -/
theorem keypairPut_credit_frame (kid : Option KeypairId) (now : Bool) :
    SameView (fun w => (peerView w,rxView w)) (keypairPut kid now) := by
  intro initial
  let P : WGWorld → Prop := fun w => (peerView w,rxView w) = initial
  have getter (id : KeypairId) : Preserves P (getKeypair id) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient key v ambient' hi hr
    obtain ⟨rfl, _, _, _, _⟩ := KeyTimes.getKeypair_return id w v key ambient ambient' hr
    exact hi
  have setter (id : KeypairId) (key : Keypair) : Preserves P (setKeypair id key) := by
    unfold setKeypair modifyDev
    apply hoare_modify
    intro w hi
    cases hd : w.dev <;> simpa [P,peerView,rxView,hd] using hi
  have owner := fun o => indexOwner_peerDeref_preserves o P
  have indices (action : IndexM Unit) : Preserves P (liftIndex action) := by
    apply hoare_liftIndex
    intro w d table hi hd
    simpa only [P,peerView,rxView,hd,Option.map_some,Option.bind_some] using hi
  change Preserves P (keypairPut kid now)
  unfold keypairPut refcountDecAndTest
  simp (config := {zeta := false}) only [branch,branchCmp,invariant,unsupported,liftM]
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head getKeypair; exact getter _)
    | (index_material_head setKeypair; exact setter _ _)
    | (index_material_head IndexOwner.peerDeref; exact owner _)
    | (index_material_head modifyDev
       unfold modifyDev
       apply hoare_modify
       intro w hi
       cases hd : w.dev <;> simpa [P,peerView,rxView,hd] using hi)
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | credit_component indices
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match
    | contradiction

theorem protected_view (hi : Protected cs loans w) (he : peerView v = peerView w) :
    Protected cs loans v := by
  intro o
  simpa only [balance_view (o := o) he] using hi o

theorem packetAt_view (he : rxView v = rxView w) : packetAt v p = packetAt w p := by
  have h := Prod.mk.inj he
  cases hv : v.dev <;> cases hw : w.dev <;>
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
    cases hw : w.dev with
    | none => simp [hd,hw] at hepoch
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
theorem paid_free (ambient : Ambient) (hi : Inventory (paid c :: cs) w)
    (hs : Protected (paid c :: cs) loans w) :
    ∃ v, ((freeRxSkb c.packet.slot).run w).run ambient = .ok (((),v),ambient) ∧
      Inventory cs v ∧ Protected cs loans v ∧ packetAt v c.packet = none := by
  obtain ⟨hep,p,hp,ho⟩ := hi.present (paid c) (by simp)
  change packetAt w c.packet = some p at hp
  cases hd : w.dev with
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
        simp_all
      simp [v,packetAt,Packets.update,hd,xe,Std.TreeMap.getElem?_erase,ne]
    refine ⟨v,Packets.freeRxSkb_run w ambient d _ p hd slot,?_,?_,?_⟩
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

/-- The literal poll cleanup cut, without a fabricated WGWorld for a Stop. -/
def cleanup (id : SkbId) (pkt : RxPacket) (releaseFlag : Bool) : WG.M Unit := do
  keypairPut (some pkt.keypair) false
  peerPut (some pkt.peer)
  _ ← branch .rxPollFree releaseFlag
  freeRxSkb id

/-- A successful literal cleanup consumes the selected credit and frees the
resident packet. No return is inferred from positivity alone. -/
theorem cleanup_discharge_normal (hi : Inventory (c :: cs) w)
    (hs : Protected (c :: cs) loans w) (phase : c.phase = .selected)
    (_hp : packetAt w c.packet = some pkt) (owner : pkt.peer = c.owner.slot)
    (ambient ambient' : Ambient)
    (hr : ((cleanup c.packet.slot pkt flag).run w).run ambient = .ok (((),v),ambient')) :
    Inventory cs v ∧ Protected cs loans v ∧ packetAt v c.packet = none := by
  simp only [cleanup,MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨u,a,ambientA,hk,u',b,ambientB,hb,value,z,ambientZ,hz,hf⟩ := hr
  cases u
  cases u'
  have hv := Prod.mk.inj ((Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
    (keypairPut_credit_frame (some pkt.keypair) false) w ambient () a ambientA hk)
  have ia := inventory_view hi hv.2
  have sa := protected_view hs hv.1
  obtain ⟨sb,rb,_⟩ := selected_payment_normal sa phase ambientA ambientB (by simpa [owner] using hb)
  have ib := inventory_paid (inventory_view ia rb)
  have hz' : z = b := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.branch .rxPollFree flag) (fun g => g = b))
    b ambientB value z ambientZ rfl hz
  subst z
  obtain ⟨out,free,iv,sv,pv⟩ := paid_free ambientZ ib sb
  rw [hf] at free
  cases free
  exact ⟨iv,sv,pv⟩

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
  cases hw : w.dev with
  | none => simp [hd,hw] at epoch
  | some old =>
    have ep : d.ifindex = old.ifindex := by simpa [peerView,hd,hw] using epoch
    cases hq : old.peers[pid]? with
    | none => simp [hd,hp,hw,hq] at slot
    | some q =>
      have fields : p.internalId = q.internalId ∧ p.refcount = q.refcount ∧ p.rxQueue = q.rxQueue := by
        simpa [peerView,hd,hp,hw,hq] using slot
      simpa [ep,fields.1,fields.2.2] using hi old pid q id hw hq

theorem queueOwners_paid (hi : QueueOwners (c :: cs) w) (hc : c.phase = .selected) :
    QueueOwners (paid c :: cs) w := by
  intro d pid p id hd hp
  simpa [List.filter_cons,paid,hc] using hi d pid p id hd hp

theorem queueOwners_paid_iff : QueueOwners (paid c :: cs) w ↔ QueueOwners cs w := by
  simp [QueueOwners,paid]


/-- Removing a peer drops its queue obligation; a nonfinal payment preserves
its queue and identity. This is the actual payment projection, not retention. -/
theorem queueOwners_paymentState (hi : QueueOwners cs w)
    (hd : w.dev = some d) (hp : d.peers[pid]? = some p) :
    QueueOwners cs (paymentState w d pid p) := by
  intro out qid q id hout hq
  have he : out = {d with peers := (if p.refcount = 1 then d.peers.erase pid else d.peers.insert pid {p with refcount := p.refcount - 1})} := by
    simpa [paymentState] using hout.symm
  subst out
  by_cases hc : p.refcount = 1
  · by_cases hpid : pid = qid
    · simp [hc,hpid] at hq
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
    (hc : c.phase = .selected) (hd : w.dev = some d) (hp : d.peers[c.owner.slot]? = some p)
    (ambient ambient' : Ambient)
    (hr : ((peerPut (some c.owner.slot)).run w).run ambient = .ok (((),v),ambient')) :
    QueueOwners (paid c :: cs) v := by
  exact queueOwners_paid
    (queueOwners_view (queueOwners_paymentState hq hd hp)
      (peerPut_effect _ w v d p ambient ambient' hd hp hr).2.1) hc

/-- Free preserves the same remaining queue ownership; a paid cell contributes
no queued occurrence, so no remaining item is silently removed from this ledger. -/
theorem paid_free_queues (hi : QueueOwners (paid c :: cs) w)
    (ambient ambient' : Ambient)
    (hr : ((freeRxSkb c.packet.slot).run w).run ambient = .ok (((),v),ambient')) :
    QueueOwners cs v := by
  have frame : Hoare (freeRxSkb c.packet.slot) (fun g => peerView g = peerView w)
      (fun _ g => peerView g = peerView w) := by
    unfold freeRxSkb
    apply hoare_liftSkb
    intro g d store hg hd
    simpa [peerView,hd] using hg
  exact queueOwners_view (queueOwners_paid_iff.mp hi)
    ((hoare_iff_run_ambient _ _ _).mp frame w ambient () v ambient' rfl hr)

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
theorem drop_selection (id : SkbId) (ambient : Ambient) (hd : w.dev = some d) (hp : d.peers[pid]? = some p)
    (peek : p.rxQueue.peeked = some id)
    (hi : Inventory (⟨⟨d.ifindex,id⟩,⟨d.ifindex,pid,p.internalId⟩,.queued⟩ :: cs) w)
    (hq : QueueOwners (⟨⟨d.ifindex,id⟩,⟨d.ifindex,pid,p.internalId⟩,.queued⟩ :: cs) w)
    (hs : Protected (⟨⟨d.ifindex,id⟩,⟨d.ifindex,pid,p.internalId⟩,.queued⟩ :: cs) loans w) :
    ∃ v, ((dropRxQueue pid).run w).run ambient = .ok (((),v),ambient) ∧
      Inventory (⟨⟨d.ifindex,id⟩,⟨d.ifindex,pid,p.internalId⟩,.selected⟩ :: cs) v ∧
      QueueOwners (⟨⟨d.ifindex,id⟩,⟨d.ifindex,pid,p.internalId⟩,.selected⟩ :: cs) v ∧
      Protected (⟨⟨d.ifindex,id⟩,⟨d.ifindex,pid,p.internalId⟩,.selected⟩ :: cs) loans v := by
  let out : Peer := {p with rxQueue := p.rxQueue.dropPeeked}
  let v := Packets.update w fun d => {d with peers := d.peers.insert pid out}
  have hr : ((dropRxQueue pid).run w).run ambient = .ok (((),v),ambient) := by
    simp [dropRxQueue,getPeer,getDev,setPeer,modifyDev,hd,hp,v,Packets.update,out]
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
      by_cases hid : id = sid <;> simp_all
      all_goals omega
    · have oldq : d.peers[qid]? = some q := by simpa [Std.TreeMap.getElem?_insert,same] using hqslot
      have old := hq d qid q sid hd oldq
      simpa [List.filter_cons,Owner.mk.injEq,same] using old
  · intro o
    rw [bal]
    exact selected_protected hs rfl o

/-- Source ENOSPC cleanup has no poll-free decision: key put, peer put, free. -/
def discard (id : SkbId) (pkt : RxPacket) : WG.M Unit := do
  keypairPut (some pkt.keypair) false
  peerPut (some pkt.peer)
  freeRxSkb id

/-- On a successful original discard, the unpublished packet's peer credit is
paid and its resident cell is freed. Remaining ledgers and queue multiplicities
survive; no totality follows from key payment alone. -/
theorem discard_unpublished_normal (hi : Inventory (c :: cs) w)
    (hs : Protected (c :: cs) loans w) (hq : QueueOwners (c :: cs) w)
    (phase : c.phase = .unpublished) (owner : pkt.peer = c.owner.slot)
    (ambient ambient' : Ambient)
    (hr : ((discard c.packet.slot pkt).run w).run ambient = .ok (((),v),ambient')) :
    Inventory cs v ∧ Protected cs loans v ∧ QueueOwners cs v ∧ packetAt v c.packet = none := by
  simp only [discard,MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨u,a,ambientA,hk,u',b,ambientB,hb,hf⟩ := hr
  cases u
  cases u'
  have hv := Prod.mk.inj ((Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
    (keypairPut_credit_frame (some pkt.keypair) false) w ambient () a ambientA hk)
  have ia := inventory_selected (inventory_view hi hv.2)
  have sa := selected_protected (protected_view hs hv.1) (by simp [phase,Phase.charged])
  have qa : QueueOwners (selected c :: cs) a := by
    have q := queueOwners_view hq hv.1
    intro d pid p id hd hp
    simpa [List.filter_cons,selected,phase] using q d pid p id hd hp
  obtain ⟨p,hp,_⟩ := selected_credit sa rfl
  obtain ⟨d,hd,_,hdp,_⟩ := resident_fields hp
  have payment : ((peerPut (some (selected c).owner.slot)).run a).run ambientA =
      .ok (((),b),ambientB) := by simpa [selected,owner] using hb
  obtain ⟨sb,rb,_⟩ := selected_payment_normal sa rfl ambientA ambientB payment
  have ib := inventory_paid (inventory_view ia rb)
  have qb := selected_payment_queues qa rfl hd hdp ambientA ambientB payment
  obtain ⟨out,free,iv,sv,pv⟩ := paid_free ambientB ib sb
  change ((freeRxSkb c.packet.slot).run b).run ambientB = .ok (((),out),ambientB) at free
  rw [hf] at free
  cases free
  exact ⟨iv,sv,paid_free_queues qb _ _ hf,pv⟩

/-- A key-payment Stop is retained by both literal cleanup cuts, with no
invented paid/free endpoint or failed WGWorld. -/
theorem cleanup_key_stop (id : SkbId) (ambient : Ambient)
    (hk : ((keypairPut (some pkt.keypair) false).run w).run ambient = .error reason) :
    ((cleanup id pkt flag).run w).run ambient = .error reason ∧
      ((discard id pkt).run w).run ambient = .error reason := by
  simp [cleanup,discard,StateT.run_bind,hk]

end Leanux.Proofs.WG.Queues.RxCredits
