import Leanux.Proofs.WG.AuthenticatedEffects.TransportHookFrames

/-! Real routing, errno and staging-splice paths leave every RX packet anchor
intact; peer lookup loans do not require an assumed peer-identity invariant. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportHookFrames
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Packets TransportCarrier
set_option maxHeartbeats 600000

theorem lookup (family addr : Nat) : SameView RxDisposition.nativeRxStore (lookupDst family addr) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  have borrowed := (hoare_iff_run_ambient _ _ _).mp
    (RxBorrow.lookupDst_spec family addr (wgStoreView w)) w a result v b rfl run
  cases result with
  | none =>
    have same : v.dev = w.dev := congrArg WGStoreView.dev borrowed
    simp only [RxDisposition.nativeRxStore,same]
  | some pid =>
    obtain ⟨d,p,device,_,_,after⟩ := borrowed
    change w.dev = some d at device
    have endpoint : v.dev = some {d with peers := d.peers.insert pid {p with refcount := p.refcount + 1}} :=
      congrArg WGStoreView.dev after
    simp only [RxDisposition.nativeRxStore,device,endpoint,Option.map_some,Option.bind_some]

theorem trim (pid : PeerId) : SameView RxDisposition.nativeRxStore (xmitTrim pid) := by
  have frame : SameView OwnerCompletion.geometry (xmitTrim pid) := by
    intro initial
    change Preserves (fun w => OwnerCompletion.geometry w = initial) _
    unfold xmitTrim
    simp only [Std.Legacy.Range.forIn_eq_forIn_range',branch]
    repeat' completion_step initial
  exact frame.factor Prod.snd

theorem splice (pid : PeerId) (packets : List Packet) :
    SameView RxDisposition.nativeRxStore (xmitSplice pid packets) := by
  unfold xmitSplice
  transport_native_rx

theorem front (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    SameView RxDisposition.nativeRxStore (txFront family addr packets mtu) := by
  intro initial
  let P := fun w => RxDisposition.nativeRxStore w = initial
  change Preserves P _
  have getter (pid : PeerId) : Preserves P (getPeer pid) := (TransportPublication.getPeer_rx pid).wp (· = initial)
  have pay (pid : Option PeerId) : Preserves P (peerPut pid) := (RxCredits.peerPut_rxView pid).wp (· = initial)
  have look : Preserves P (lookupDst family addr) := (lookup family addr).wp (· = initial)
  have trimming (pid : PeerId) : Preserves P (xmitTrim pid) := (trim pid).wp (· = initial)
  have splicing (pid : PeerId) (ps : List Packet) : Preserves P (xmitSplice pid ps) := (splice pid ps).wp (· = initial)
  have loopback (sites : List HiddenSite) (raised : Bool) : Preserves P (loopbackSend sites raised) :=
    (TransportPublication.store_rx _ (loopbackSend_kernel sites raised)).wp (· = initial)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have routing {α : Type} (a : Net.M α) : Preserves P (monadLift a : WG.M α) :=
    (TransportPublication.store_rx _ (liftRouting_sameWGStore a)).wp (· = initial)
  have errors : Preserves P (modifyDev fun d => {d with txErrors := d.txErrors + 1}) :=
    (modifyDev_rx (fun d => {d with txErrors := d.txErrors + 1}) (fun _ => rfl) (fun _ => rfl)).wp (· = initial)
  have loop {α β : Type} (xs : List α) (init : β) (f : α → β → WG.M (ForInStep β))
      (hf : ∀ x b, Preserves P (f x b)) : Preserves P (forIn xs init f) :=
    list_view_spec RxDisposition.nativeRxStore (· = initial) xs init f hf
  rxstack_preserves_source [txFront,txCheck,txSelect,txError,txHeaders,txWalk,
      WG.andM,branch,invariant,skipCutSites,envOk]
    using [getter,look,trimming,splicing,pay,loopback,ambient,routing,errors,loop]

end Leanux.Proofs.WG.AuthenticatedEffects.TransportHookFrames
