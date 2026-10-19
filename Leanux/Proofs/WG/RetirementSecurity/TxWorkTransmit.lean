import Leanux.Proofs.WG.RetirementSecurity.TxWorkRxPoll

/-! Native routing/selection and plaintext staging edits retain existing TX
service. Actual transmit enters staged allocation once, then pays its selected
peer reference without losing any remaining queue-head obligation. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem service_store {action : WG.M α} (same : SameWGStore action) :
    Preserves (Obligations crypt tx) action :=
  passive (cryptWire_store same) (ownership_queues (ownershipPoints_kernel _ same)) (store same)

theorem trim_service (pid : PeerId) : Preserves (Obligations crypt tx) (xmitTrim pid) := by
  apply passive ?_ ((xmitTrim_protect pid).factor (fun s=>s.2.2.1)) ?_
  · intro initial
    change Preserves (fun w=>txCryptWire w=initial) _
    unfold xmitTrim
    simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',branch]
    repeat' first
      | (rx_retention_head ForIn.forIn
         apply list_view_spec id (fun w=>txCryptWire w=initial)
         intro x state
         change Preserves (fun w=>txCryptWire w=initial) _)
      | crypt_wire_step initial
  · intro initial
    change Preserves (fun w=>queued w=initial) _
    unfold xmitTrim
    simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',branch]
    repeat' first
      | (rx_retention_head ForIn.forIn
         apply list_view_spec id (fun w=>queued w=initial)
         intro x state
         change Preserves (fun w=>queued w=initial) _)
      | tx_work_step initial

theorem splice_service (pid : PeerId) (packets : List WG.Packet) :
    Preserves (Obligations crypt tx) (xmitSplice pid packets) := by
  apply passive ?_ ((xmitSplice_protect pid packets).factor (fun s=>s.2.2.1)) ?_
  · intro initial
    change Preserves (fun w=>txCryptWire w=initial) _
    unfold xmitSplice
    repeat' crypt_wire_step initial
  · intro initial
    change Preserves (fun w=>queued w=initial) _
    unfold xmitSplice
    repeat' tx_work_step initial

theorem lookup_service (family addr : Nat) : Preserves (Obligations crypt tx) (lookupDst family addr) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have borrowed:=(hoare_iff_run_ambient _ _ _).mp (RxBorrow.lookupDst_spec family addr (wgStoreView w))
    w a result v b rfl run
  cases result with
  | none=>
    have same:v.dev=w.dev := congrArg WGStoreView.dev borrowed
    apply before.frame
    · funext pid; simp only [handoffTxView,same]
    · funext id; simp only [TxDisposition.txPackets,same]
    · simp only [txCryptItems,same]
    · simp only [queued,same]
  | some pid=>
    obtain ⟨d,p,device,found,_,after⟩:=borrowed
    change w.dev=some d at device
    have endpoint:v.dev=some {d with peers:=d.peers.insert pid {p with refcount:=p.refcount+1}} :=
      congrArg WGStoreView.dev after
    apply before.frame
    · funext other
      by_cases same:pid=other
      · subst other; simp [handoffTxView,endpoint,device,found]
      · simp [handoffTxView,endpoint,device,Std.TreeMap.getElem?_insert,same]
    · funext id; simp [TxDisposition.txPackets,endpoint,device]
    · simp [txCryptItems,endpoint,device]
    · simp [queued,endpoint,device]

theorem errors_service : Preserves (Obligations crypt tx)
    (modifyDev fun d=>{d with txErrors:=d.txErrors+1}) := by
  apply passive
  · intro initial
    change Preserves (fun w=>txCryptWire w=initial) _
    repeat' crypt_wire_step initial
  · exact ownership_queues (ownership_modifyDev _ (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl))
  · exact modify _ (fun _=>rfl)

theorem front_service (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    Preserves (Obligations crypt tx) (Packets.txFront family addr packets mtu) := by
  let P:=Obligations crypt tx
  have getter (pid : PeerId) : Preserves P (getPeer pid) := getPeer_preserves _ _
  have pay (pid : Option PeerId) : Preserves P (peerPut pid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b before run
    cases result
    exact before.peer_put pid a b run
  have look:=lookup_service (crypt:=crypt) (tx:=tx) family addr
  have trimming:=trim_service (crypt:=crypt) (tx:=tx)
  have splicing:=splice_service (crypt:=crypt) (tx:=tx)
  have loopback (sites : List HiddenSite) (raised : Bool) : Preserves P (loopbackSend sites raised) :=
    service_store (loopbackSend_kernel sites raised)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have routing {α : Type} (a : Net.M α) : Preserves P (monadLift a : WG.M α) :=
    service_store (liftRouting_sameWGStore a)
  have errors:Preserves P _:=errors_service
  have loop {α β : Type} (xs : List α) (init : β) (f : α→β→WG.M (ForInStep β))
      (hf : ∀x b,Preserves P (f x b)) : Preserves P (forIn xs init f) := list_view_spec id P xs init f hf
  change Preserves P _
  rxstack_preserves_source [Packets.txFront,Packets.txCheck,Packets.txSelect,Packets.txError,
      Packets.txHeaders,Packets.txWalk,WG.andM,branch,invariant,skipCutSites,envOk]
    using [getter,look,trimming,splicing,pay,loopback,ambient,routing,errors,loop]

theorem transmit_service (before : StageReady locals crypt tx w) (family addr : Nat)
    (packets : List WG.Packet) (mtu : Nat) (a b : Ambient)
    (run : ((wgXmit family addr packets mtu).run w).run a=.ok ((result,v),b)) : Obligations crypt tx v := by
  rw [Packets.wgXmit_front_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨selected,u,c,frontRun,tail⟩:=run
  have service:=(hoare_iff_run_ambient _ _ _).mp (front_service family addr packets mtu)
    w a selected u c before.1 frontRun
  cases selected with
  | error err=>cases tail; exact service
  | ok pid=>
    have owned:=(hoare_iff_run_ambient _ _ _).mp (TransmitOccurrences.front family addr packets mtu)
      w a (.ok pid) u c ⟨before.2.1.1,before.2.1.2,before.2.2⟩ frontRun
    simp only [Packets.txTail,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨_,t,e,staged,_,s,f,paid,done⟩:=tail
    cases done
    exact (staged_service ⟨service,⟨owned.1,owned.2.1⟩,owned.2.2⟩ pid c e staged).peer_put (some pid) e b paid

theorem serving_transmit (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    Preserves (fun w:World=>Serving locals crypt tx w.wg) (liftWG (wgXmit family addr packets mtu)) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  have native:=HolderPoll.native_receipt run
  exact ⟨transmit_service before.stage_ready family addr packets mtu w.ambient v.ambient native,
    (hoare_iff_run _ _ _).mp
      (TxCovered.product_join (OccurrenceStack.transmit family addr packets mtu)
        (TxCoverageStack.transmit family addr packets mtu)) w result v before.2 run⟩

end Leanux.Proofs.WG.RetirementSecurity.TxWork
