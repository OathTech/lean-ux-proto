import Leanux.Proofs.WG.RetirementSecurity.TxCoverageNative
import Leanux.Proofs.WG.RetirementSecurity.TransmitEntryOccurrences

/-! Native transmit entry preserves converse coverage of allocated TX cells.
Routing failures and staged plaintext edits do not remove allocated cells;
the actual staged-send and final peer payment preserve their ownership. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxCoverageTraffic
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits TxCoverageNative
variable {locals : List TxLocalBatch}

theorem trim (pid : PeerId) : Preserves (Inv (locals:=locals)) (xmitTrim pid) := by
  apply wire ((xmitTrim_protect pid).factor (fun s => s.2.2.1))
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold xmitTrim
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',branch]
  repeat' first
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w => txCryptWire w = initial)
       intro x b
       change Preserves (fun w => txCryptWire w = initial) _)
    | crypt_wire_step initial

theorem splice (pid : PeerId) (packets : List WG.Packet) : Preserves (Inv (locals:=locals)) (xmitSplice pid packets) := by
  apply wire ((xmitSplice_protect pid packets).factor (fun s => s.2.2.1))
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold xmitSplice
  repeat' crypt_wire_step initial

theorem lookup (family addr : Nat) : Preserves (Inv (locals:=locals)) (lookupDst family addr) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have borrowed := (hoare_iff_run_ambient _ _ _).mp
    (RxBorrow.lookupDst_spec family addr (wgStoreView w)) w a result v b rfl run
  have fields : (handoffTxView v,TxDisposition.txPackets v)=(handoffTxView w,TxDisposition.txPackets w) := by
    cases result with
    | none =>
      have same : v.dev = w.dev := congrArg WGStoreView.dev borrowed
      apply Prod.ext
      · funext pid; simp only [handoffTxView,same]
      · funext id; simp only [TxDisposition.txPackets,same]
    | some pid =>
      obtain ⟨d,p,device,found,_,after⟩ := borrowed
      change w.dev = some d at device
      have endpoint : v.dev = some {d with peers := d.peers.insert pid {p with refcount := p.refcount + 1}} :=
        congrArg WGStoreView.dev after
      apply Prod.ext
      · funext other
        by_cases same : pid = other
        · subst other; simp [handoffTxView,endpoint,device,found]
        · simp [handoffTxView,endpoint,device,Std.TreeMap.getElem?_insert,same]
      · funext id; simp [TxDisposition.txPackets,endpoint,device]
  exact before.cells (congrArg Prod.snd fields) (queueContents_of_exact (congrArg Prod.fst fields))

theorem errors : Preserves (Inv (locals:=locals)) (modifyDev fun d => {d with txErrors := d.txErrors + 1}) :=
  modify_device _ (fun _ => rfl) (fun _ => rfl)

theorem front (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    Preserves (Inv (locals:=locals)) (Packets.txFront family addr packets mtu) := by
  have getter (pid : PeerId) : Preserves (Inv (locals:=locals)) (getPeer pid) := getPeer_preserves _ _
  have pay := peer_put (locals:=locals)
  have look := lookup (locals:=locals) family addr
  have trimming := trim (locals:=locals)
  have splicing := splice (locals:=locals)
  have loopback (sites : List HiddenSite) (raised : Bool) : Preserves (Inv (locals:=locals)) (loopbackSend sites raised) :=
    store (loopbackSend_kernel sites raised)
  have ambient {α : Type} (a : AmbientM α) : Preserves (Inv (locals:=locals)) (monadLift a : WG.M α) :=
    hoare_liftAmbient a (Inv (locals:=locals))
  have routing {α : Type} (a : Net.M α) : Preserves (Inv (locals:=locals)) (monadLift a : WG.M α) :=
    store (liftRouting_sameWGStore a)
  have errors := errors (locals:=locals)
  have loop {α β : Type} (xs : List α) (init : β) (f : α → β → WG.M (ForInStep β))
      (hf : ∀ x b,Preserves (Inv (locals:=locals)) (f x b)) : Preserves (Inv (locals:=locals)) (forIn xs init f) :=
    list_view_spec id (Inv (locals:=locals)) xs init f hf
  rxstack_preserves_source [Packets.txFront,Packets.txCheck,Packets.txSelect,Packets.txError,
      Packets.txHeaders,Packets.txWalk,WG.andM,branch,invariant,skipCutSites,envOk]
    using [getter,look,trimming,splicing,pay,loopback,ambient,routing,errors,loop]


theorem transmit (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    Preserves (Inv (locals:=locals)) (wgXmit family addr packets mtu) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  rw [Packets.wgXmit_front_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨selected,u,c,frontRun,tail⟩:=run
  have held := (hoare_iff_run_ambient _ _ _).mp (front family addr packets mtu)
    w a selected u c before frontRun
  cases selected with
  | error err => cases tail; exact held
  | ok pid =>
    simp only [Packets.txTail,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨_,t,e,stage,_,s,f,paid,done⟩:=tail
    cases done
    exact (held.staged pid c e stage).peer_put (some pid) e b paid

end Leanux.Proofs.WG.RetirementSecurity.TxCoverageTraffic
