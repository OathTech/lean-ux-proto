import Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertextNativeHandshake

/-! Native cryptokey-routing selection edits staged plaintext and metadata.
Every surviving queued batch keeps its packet bytes and marks before staged send. -/
namespace Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertext.Transmit
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity Queues.RxCredits Native
set_option maxHeartbeats 600000
set_option pp.structureInstances false

theorem trim (pid : PeerId) : Preserves Inv (xmitTrim pid) := by
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

theorem splice (pid : PeerId) (packets : List WG.Packet) : Preserves Inv (xmitSplice pid packets) := by
  apply wire ((xmitSplice_protect pid packets).factor (fun s => s.2.2.1))
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold xmitSplice
  repeat' crypt_wire_step initial

theorem lookup (family addr : Nat) : Preserves Inv (lookupDst family addr) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have borrowed := (hoare_iff_run_ambient _ _ _).mp
    (RxBorrow.lookupDst_spec family addr (wgStoreView w)) w a result v b rfl run
  apply before.frame
  dsimp only [view]
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

theorem errors : Preserves Inv (modifyDev fun d => {d with txErrors := d.txErrors + 1}) :=
  modify_device _ (fun _ => rfl) (fun _ => rfl)

theorem front (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    Preserves (Inv) (Packets.txFront family addr packets mtu) := by
  have getter (pid : PeerId) : Preserves (Inv) (getPeer pid) := getPeer_preserves _ _
  have pay := peer_put
  have look := lookup family addr
  have trimming := trim
  have splicing := splice
  have loopback (sites : List HiddenSite) (raised : Bool) : Preserves (Inv) (loopbackSend sites raised) :=
    store (loopbackSend_kernel sites raised)
  have ambient {α : Type} (a : AmbientM α) : Preserves (Inv) (monadLift a : WG.M α) :=
    hoare_liftAmbient a (Inv)
  have routing {α : Type} (a : Net.M α) : Preserves (Inv) (monadLift a : WG.M α) :=
    store (liftRouting_sameWGStore a)
  have errors := errors
  have loop {α β : Type} (xs : List α) (init : β) (f : α → β → WG.M (ForInStep β))
      (hf : ∀ x b,Preserves (Inv) (f x b)) : Preserves (Inv) (forIn xs init f) :=
    list_view_spec id (Inv) xs init f hf
  rxstack_preserves_source [Packets.txFront,Packets.txCheck,Packets.txSelect,Packets.txError,
      Packets.txHeaders,Packets.txWalk,WG.andM,branch,invariant,skipCutSites,envOk]
    using [getter,look,trimming,splicing,pay,loopback,ambient,routing,errors,loop]


theorem transmit (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    Preserves (Coherent locals active) (wgXmit family addr packets mtu) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have physical : OccurrenceStack.Ready locals active v :=
    ⟨before.1.1.transmit family addr packets mtu a b run,
      TransmitOccurrences.transmit ⟨before.1.1.bounded,before.1.2⟩ family addr packets mtu a b run⟩
  refine ⟨physical,?_⟩
  rw [Packets.wgXmit_front_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨selected,u,c,frontRun,tail⟩ := run
  have held := (hoare_iff_run_ambient _ _ _).mp (front family addr packets mtu)
    w a selected u c before.2 frontRun
  have owners := (hoare_iff_run_ambient _ _ _).mp (TransmitOccurrences.front family addr packets mtu)
    w a selected u c ⟨before.1.1.bounded,before.1.2⟩ frontRun
  cases selected with
  | error err => cases tail; exact held
  | ok pid =>
    simp only [Packets.txTail,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨_,t,e,staged,_,s,f,paid,done⟩ := tail
    cases done
    have kept := ReadyCiphertext.send ⟨⟨owners.1,owners.2.1⟩,held⟩ pid c e staged
    exact (hoare_iff_run_ambient _ _ _).mp (peer_put (some pid)) t e () v b kept paid

end Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertext.Transmit
