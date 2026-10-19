import Leanux.Proofs.WG.AuthenticatedEffects.EmissionStagingFrames
import Leanux.Proofs.WG.Packets.TxFront
import Leanux.Proofs.WG.AuthenticatedEffects.TransportFrontFrames

/-! Native routing lookup, staged splice and receive finish preserve sent.
Trie and packet-store projections alone would not establish this frame. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.EmissionFrames
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do Lifetimes Packets
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem aip_spec (P : List SentDatagram → Prop) {α : Type} (action : AipM α) :
    Preserves (fun w => P w.sent) (liftAip action) :=
  hoare_liftAip action _ (fun _ _ _ hi _ => hi)

theorem lookup (root : Option NodeId) (bits key : Nat) : SameView WGWorld.sent (WG.lookup root bits key) := by
  sent_frame [WG.lookup,swapEndian] using [peerGetMaybeZero_sent_spec]
  all_goals
    apply hoare_liftAip
    intro w d nodes hi hd
    exact hi

theorem lookup_spec (P : List SentDatagram → Prop) (root : Option NodeId) (bits key : Nat) :
    Preserves (fun w => P w.sent) (WG.lookup root bits key) := (lookup root bits key).wp P

theorem lookup_dst (family addr : Nat) : SameView WGWorld.sent (lookupDst family addr) := by
  sent_frame [lookupDst] using [lookup_spec]

theorem lookup_src (protocol : Nat) (bytes : List UInt8) : SameView WGWorld.sent (lookupSrc protocol bytes) := by
  sent_frame [lookupSrc] using [lookup_spec]

theorem receive_finish (pid : PeerId) (ready : RxReady) : SameView WGWorld.sent (rxFinish pid ready) := by
  have look (P : List SentDatagram → Prop) : Preserves (fun w => P w.sent)
      (lookupSrc ready.protocol ready.bytes) := (lookup_src ready.protocol ready.bytes).wp P
  sent_frame [rxFinish,rxAfterLookup,dishonest,updateRxStats] using [look,peerPut_sent_spec,getPeer_sent_spec,setPeer_sent_spec]

theorem endpoint_value (pid : PeerId) (ep : Endpoint) : SameView WGWorld.sent (setPeerEndpoint pid ep) := by
  sent_frame [setPeerEndpoint,endpointEq,dstCacheReset,requireNotPending,getAmbient,hiddenJiffies]
    using [getPeer_sent_spec,setPeer_sent_spec]

private theorem loopback (sites : List HiddenSite) (raised : Bool) : SameView WGWorld.sent (loopbackSend sites raised) := by
  sent_frame [loopbackSend,raiseLoopbackRx,loopbackSoftirq,getAmbient,peekHiddenSite] using []
  all_goals
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a value v b hi run
    cases run

private theorem loop_spec (P : WGWorld → Prop) {α β : Type} (xs : List α) (init : β)
    (body : α → β → WG.M (ForInStep β)) (safe : ∀ value state, Preserves P (body value state)) :
    Preserves P (forIn xs init body) := list_view_spec (fun w : WGWorld => w) P xs init body safe

private theorem trim (pid : PeerId) : SameView WGWorld.sent (xmitTrim pid) := by
  intro initial
  change Preserves (fun w : WGWorld => w.sent = initial) _
  unfold xmitTrim
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',branch]
  repeat' first
    | (cookie_source_head ForIn.forIn
       apply loop_spec (fun w : WGWorld => w.sent = initial)
       intro value state)
    | consumer_sent_step initial

theorem front (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    SameView WGWorld.sent (txFront family addr packets mtu) := by
  intro initial
  let P := fun w : WGWorld => w.sent = initial
  change Preserves P _
  have getter (pid : PeerId) : Preserves P (getPeer pid) := getPeer_sent_spec (· = initial) pid
  have pay (pid : Option PeerId) : Preserves P (peerPut pid) := peerPut_sent_spec (· = initial) pid
  have look : Preserves P (lookupDst family addr) := (lookup_dst family addr).wp (· = initial)
  have trimming (pid : PeerId) : Preserves P (xmitTrim pid) := (trim pid).wp (· = initial)
  have splicing (pid : PeerId) (ps : List Packet) : Preserves P (xmitSplice pid ps) := by
    have framed : SameView WGWorld.sent (xmitSplice pid ps) := by
      sent_frame [xmitSplice] using [getPeer_sent_spec,setPeer_sent_spec]
    exact framed.wp (· = initial)
  have localSend (sites : List HiddenSite) (raised : Bool) : Preserves P (loopbackSend sites raised) :=
    (loopback sites raised).wp (· = initial)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have routing {α : Type} (a : Net.M α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftRouting a P (fun _ _ hi => hi)
  have errors : Preserves P (modifyDev fun d => {d with txErrors := d.txErrors + 1}) := by
    apply hoare_modify
    intro w hi
    exact hi
  have loop {α β : Type} (xs : List α) (init : β) (f : α → β → WG.M (ForInStep β))
      (hf : ∀ x b, Preserves P (f x b)) : Preserves P (forIn xs init f) :=
    list_view_spec id P xs init f hf
  rxstack_preserves_source [txFront,txCheck,txSelect,txError,txHeaders,txWalk,
      WG.andM,branch,invariant,skipCutSites,envOk]
    using [getter,look,trimming,splicing,pay,localSend,ambient,routing,errors,loop]

end Leanux.Proofs.WG.AuthenticatedEffects.EmissionFrames
