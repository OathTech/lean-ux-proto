import Leanux.Proofs.WG.RetirementSecurity.HandshakeQueueCallbacks
import Leanux.Proofs.WG.RetirementSecurity.HandshakeQueueWorker
import Leanux.Proofs.WG.TransmitSecurity.HeaderLength

/-! Header-checked admission is the only producer of handshake ring payloads.
The proof follows the original prepare/drop and full-ring branches; no input
shape premise survives the complete UDP receive contract. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Std.Do
open TransmitSecurity

abbrev Valid := HeaderLength.Valid
abbrev QueueValid := Inv Valid

theorem consumeData_cell (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    SameView view (consumeData msg src ds) := by
  have cpu := fun last=>kernel (cpumaskNextOnlineFrom_sameStore last)
  handshake_cell_source [consumeData,keypairGetNull,enqueuePerDeviceAndPeerRx,enqueuePerPeerRx]
    using [cpu,indexLookup_frame,keypairGet_cell,keypairPut_cell,peerGet_frame,peerPut_frame]
  all_goals simp only [monadLift_self]
  all_goals handshake_cell_source [] using [peerGet_frame,peerPut_frame]

theorem produce_preserves (msg : List UInt8) (src : SkbSource) (valid : Valid msg) :
    Preserves QueueValid (modifyDev fun d=>{d with
      handshakeQueue:=d.handshakeQueue.produce (msg,src),handshakeQueueLen:=d.handshakeQueueLen+1}) := by
  apply hoare_modify
  intro w before d found
  cases device : w.dev with
  | none=> simp only [device,Option.map_none] at found; cases found
  | some old=>
    simp only [device,Option.map_some,Option.some.injEq] at found
    subst d
    exact produce _ _ _ (before old device) valid

def packetTail (msg : List UInt8) (src : SkbSource) : WG.M Unit := do
  let t:=messageType msg
  if ←branch .rxHandshake (t==MESSAGE_HANDSHAKE_INITIATION || t==MESSAGE_HANDSHAKE_RESPONSE || t==MESSAGE_HANDSHAKE_COOKIE) then
    if ←branch .rxRngNotReady false then unsupported "unreachable"
    _ ←branch .rxQueueBusy ((←getDev).handshakeQueueLen>MAX_QUEUED_INCOMING_HANDSHAKES/2)
    if ←branch .rxProduceFailed (←getDev).handshakeQueue.full then return
    modifyDev fun d=>{d with handshakeQueue:=d.handshakeQueue.produce (msg,src),handshakeQueueLen:=d.handshakeQueueLen+1}
    cpumaskNextOnline
    queueDeviceWork .receiveWorker
    return
  if ←branch .rxData (t==MESSAGE_DATA) then
    let ds ←ipTunnelGetDsfield (if src.family==4 then ETH_P_IP else ETH_P_IPV6) (outerDsBytes src)
    consumeData msg src ds
    return
  invariant "validate_header_len admitted an unknown type"

theorem packet_factor (msg : List UInt8) (src : SkbSource) : packetReceive msg src=(do
    if ←branch .rxPrepareFailed !(←prepareSkbHeader msg) then return
    packetTail msg src) := rfl

theorem packet_tail (msg : List UInt8) (src : SkbSource) (valid : Valid msg) :
    Preserves QueueValid (packetTail msg src) := by
  have cpu : SameView view cpumaskNextOnline := by handshake_cell_source [cpumaskNextOnline] using []
  have get := frame (Valid:=Valid) (kernel getDev_sameWGStore)
  have consume := fun ds=>frame (Valid:=Valid) (consumeData_cell msg src ds)
  have ds := fun protocol bytes=>frame (Valid:=Valid) ((ipTunnelGetDsfield_sameWGWorld protocol bytes).factor view)
  have mask := frame (Valid:=Valid) cpu
  have offer := produce_preserves msg src valid
  have ambient {α : Type} (a : AmbientM α) : Preserves QueueValid (monadLift a : WG.M α) := hoare_liftAmbient a _
  rxstack_preserves_source [packetTail,branch,invariant,unsupported,queueDeviceWork]
    using [get,consume,ds,mask,offer,ambient]

theorem packet_receive (msg : List UInt8) (src : SkbSource) : Preserves QueueValid (packetReceive msg src) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  rw [packet_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨accepted,u,c,header,tail⟩:=run
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp (prepareSkbHeader_sameWGWorld msg) w a accepted u c header
  change u=w at same
  subst u
  rw [MaterialOrigin.bind_ok_ambient] at tail
  obtain ⟨refused,u,c',guard,rest⟩:=tail
  have equation : ((!accepted,w),CounterWindow.record c .rxPrepareFailed (!accepted))=((refused,u),c') := by
    simpa [branch,AmbientM.branch,CounterWindow.record] using guard
  cases accepted <;> simp only [Bool.not_false,Bool.not_true] at equation
  all_goals obtain ⟨⟨rfl,rfl⟩,rfl⟩:=Prod.mk.inj equation
  · cases rest
    exact before
  · exact (hoare_iff_run_ambient _ _ _).mp (packet_tail msg src (HeaderLength.prepared msg w w a c header))
      w _ result v b before rest

theorem receive (msg : List UInt8) (src : SkbSource) : Preserves QueueValid (wgReceive msg src) := by
  have packet := packet_receive msg src
  have ambient {α : Type} (a : AmbientM α) : Preserves QueueValid (monadLift a : WG.M α) := hoare_liftAmbient a _
  rxstack_preserves_source [wgReceive,branch,unsupported] using [packet,ambient]

theorem fixture_valid (net bare : Bool) : QueueValid (Runner.initialWG net bare) := by
  intro d found
  cases net <;> cases bare <;> simp only [Runner.initialWG,Bool.not_false,Bool.not_true,
    Bool.false_and,Bool.true_and,↓reduceIte] at found
  all_goals solve
    | cases found
    | (cases found; exact initial _ _)

end Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths
