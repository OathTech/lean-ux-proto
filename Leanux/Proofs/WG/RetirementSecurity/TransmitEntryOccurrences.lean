import Leanux.Proofs.WG.RetirementSecurity.TransmitEntryHolders
import Leanux.Proofs.WG.Packets.TxFront

/-! Full native transmit entry preserves physical TX ownership and pending
encryption aliases, including errno paths and the final nullable peer payment.
Only the real staged-send call allocates and publishes new TX occurrences. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Std.Do
open Queues.RxCredits StagingOccurrences
namespace TransmitOccurrences
abbrev Ready (locals : List TxLocalBatch) (active : List (List SkbId)) (w : WGWorld) :=
  Packets.Inv w ∧ TxOccurrences locals active w

theorem passive {action : WG.M α} (geom : SameView geometry action)
    (wire : SameView txCryptWire action) (queues : SameView handoffTxView action) :
    Preserves (Ready locals active) action :=
  TransmitEntry.joined (geometry_bound geom) (occurrence_passive wire queues)

theorem store {action : WG.M α} (same : SameWGStore action) : Preserves (Ready locals active) action :=
  passive (same.of_factor (fun s => geometry {dev := s.dev}) geometry (fun _ => rfl))
    (cryptWire_store same) (ownership_queues (ownershipPoints_kernel _ same))

theorem trim (pid : PeerId) : Preserves (Ready locals active) (xmitTrim pid) := by
  apply passive
  · intro initial
    change Preserves (fun w => geometry w = initial) _
    unfold xmitTrim
    simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',branch]
    repeat' staging_geometry_step initial
  · intro initial
    change Preserves (fun w => txCryptWire w = initial) _
    unfold xmitTrim
    simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',branch]
    repeat' first
      | (rx_retention_head ForIn.forIn
         apply list_view_spec id (fun w => txCryptWire w = initial)
         intro x b
         change Preserves (fun w => txCryptWire w = initial) _)
      | crypt_wire_step initial
  · exact (xmitTrim_protect pid).factor (fun s => s.2.2.1)

theorem splice (pid : PeerId) (packets : List WG.Packet) :
    Preserves (Ready locals active) (xmitSplice pid packets) := by
  apply passive
  · intro initial
    change Preserves (fun w => geometry w = initial) _
    unfold xmitSplice
    repeat' staging_geometry_step initial
  · intro initial
    change Preserves (fun w => txCryptWire w = initial) _
    unfold xmitSplice
    repeat' crypt_wire_step initial
  · exact (xmitSplice_protect pid packets).factor (fun s => s.2.2.1)

theorem peer_put (pid : Option PeerId) : Preserves (Ready locals active) (peerPut pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases result
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (geometry_bound (peer_put_geometry pid))
    w a () v b before.1 run,before.2.1.peer_put pid a b run,before.2.2.peer_put pid a b run⟩

theorem lookup (family addr : Nat) : Preserves (Ready locals active) (lookupDst family addr) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have borrowed := (hoare_iff_run_ambient _ _ _).mp
    (RxBorrow.lookupDst_spec family addr (wgStoreView w)) w a result v b rfl run
  cases result with
  | none =>
    have same : v.dev = w.dev := congrArg WGStoreView.dev borrowed
    have wire : txCryptWire v = txCryptWire w := by simp only [txCryptWire,TxRing.nativeCell,TxDisposition.txPackets,same]
    have queues : handoffTxView v = handoffTxView w := by funext pid; simp only [handoffTxView,same]
    exact ⟨by simpa only [Packets.Inv,Packets.snapshot,same] using before.1,
      before.2.1.wire_queues wire queues,
      before.2.2.frame_packets (congrArg Prod.fst wire) (fun _ owned => owned.queues queues) (congrArg Prod.snd wire)⟩
  | some pid =>
    obtain ⟨d,p,device,found,_,after⟩ := borrowed
    change w.dev = some d at device
    have endpoint : v.dev = some {d with peers := d.peers.insert pid {p with refcount := p.refcount + 1}} :=
      congrArg WGStoreView.dev after
    have wire : txCryptWire v = txCryptWire w := by simp [txCryptWire,TxRing.nativeCell,TxDisposition.txPackets,endpoint,device]
    have queues : handoffTxView v = handoffTxView w := by
      funext other
      by_cases same : pid = other
      · subst other; simp [handoffTxView,endpoint,device,found]
      · simp [handoffTxView,endpoint,device,Std.TreeMap.getElem?_insert,same]
    exact ⟨by simpa only [Packets.Inv,Packets.snapshot,Packets.deviceStore,endpoint,device] using before.1,
      before.2.1.wire_queues wire queues,
      before.2.2.frame_packets (congrArg Prod.fst wire) (fun _ owned => owned.queues queues) (congrArg Prod.snd wire)⟩

theorem errors : Preserves (Ready locals active) (modifyDev fun d => {d with txErrors := d.txErrors + 1}) := by
  apply passive
  · intro initial
    change Preserves (fun w => geometry w = initial) _
    repeat' staging_geometry_step initial
  · intro initial
    change Preserves (fun w => txCryptWire w = initial) _
    repeat' crypt_wire_step initial
  · exact ownership_queues (ownership_modifyDev _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))

theorem front (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    Preserves (Ready locals active) (Packets.txFront family addr packets mtu) := by
  have getter (pid : PeerId) : Preserves (Ready locals active) (getPeer pid) := getPeer_preserves _ _
  have pay := peer_put (locals := locals) (active := active)
  have look := lookup (locals := locals) (active := active) family addr
  have trimming := trim (locals := locals) (active := active)
  have splicing := splice (locals := locals) (active := active)
  have loopback (sites : List HiddenSite) (raised : Bool) : Preserves (Ready locals active) (loopbackSend sites raised) :=
    store (loopbackSend_kernel sites raised)
  have ambient {α : Type} (a : AmbientM α) : Preserves (Ready locals active) (monadLift a : WG.M α) :=
    hoare_liftAmbient a (Ready locals active)
  have routing {α : Type} (a : Net.M α) : Preserves (Ready locals active) (monadLift a : WG.M α) :=
    store (liftRouting_sameWGStore a)
  have errors := errors (locals := locals) (active := active)
  have loop {α β : Type} (xs : List α) (init : β) (f : α → β → WG.M (ForInStep β))
      (hf : ∀ x b,Preserves (Ready locals active) (f x b)) : Preserves (Ready locals active) (forIn xs init f) :=
    list_view_spec id (Ready locals active) xs init f hf
  rxstack_preserves_source [Packets.txFront,Packets.txCheck,Packets.txSelect,Packets.txError,
      Packets.txHeaders,Packets.txWalk,WG.andM,branch,invariant,skipCutSites,envOk]
    using [getter,look,trimming,splicing,pay,loopback,ambient,routing,errors,loop]

theorem transmit (before : Ready locals active w) (family addr : Nat)
    (packets : List WG.Packet) (mtu : Nat) (a b : Ambient)
    (run : ((wgXmit family addr packets mtu).run w).run a = .ok ((result,v),b)) :
    TxOccurrences locals active v := by
  rw [Packets.wgXmit_front_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨selected,u,c,frontRun,tail⟩ := run
  have held := (hoare_iff_run_ambient _ _ _).mp (front family addr packets mtu)
    w a selected u c before frontRun
  cases selected with
  | error err => cases tail; exact held.2
  | ok pid =>
    simp only [Packets.txTail,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨_,t,e,staged,_,s,f,paid,done⟩ := tail
    cases done
    have kept := CryptStaging.staged ⟨⟨held.1,held.2.1⟩,held.2.2⟩ pid c e staged
    exact ⟨kept.1.peer_put (some pid) e b paid,kept.2.peer_put (some pid) e b paid⟩

end TransmitOccurrences
end Leanux.Proofs.WG.RetirementSecurity
