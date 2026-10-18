import Leanux.Proofs.WG.Queues.AdmissionPath
import Leanux.Proofs.WG.Queues.HolderEncryptFrames

/-! The actual receive entry up to its possible data-admission call. The
factor is valid for every outcome; ledger conclusions below concern normal
returns only. No new observer replaces the existing lifetime journal. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.AdmissionReceive
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders CounterWindow

def packetFront (msg : List UInt8) (src : SkbSource) : WG.M (Option Nat) := do
  if ← branch .rxPrepareFailed !(← prepareSkbHeader msg) then return none
  let t := messageType msg
  if ← branch .rxHandshake (t == MESSAGE_HANDSHAKE_INITIATION || t == MESSAGE_HANDSHAKE_RESPONSE
                            || t == MESSAGE_HANDSHAKE_COOKIE) then
    if ← branch .rxRngNotReady false then unsupported "unreachable"
    _ ← branch .rxQueueBusy ((← getDev).handshakeQueueLen > MAX_QUEUED_INCOMING_HANDSHAKES / 2)
    if ← branch .rxProduceFailed (← getDev).handshakeQueue.full then return none
    modifyDev (appendHandshakeQueue msg src)
    cpumaskNextOnline
    queueDeviceWork .receiveWorker
    return none
  if ← branch .rxData (t == MESSAGE_DATA) then
    let ds ← ipTunnelGetDsfield (if src.family == 4 then ETH_P_IP else ETH_P_IPV6) (outerDsBytes src)
    return some ds
  invariant "validate_header_len admitted an unknown type"

def front (msg : List UInt8) (src : SkbSource) : WG.M (Option Nat) := do
  if ← branch .rxNoSock false then unsupported "unreachable"
  if ← branch .rxNoWg false then unsupported "unreachable"
  packetFront msg src

theorem packet_factor (msg : List UInt8) (src : SkbSource) :
    packetReceive msg src = (do
      match ← packetFront msg src with
      | none => pure ()
      | some ds => consumeData msg src ds) := by
  have stopped {α β : Type} (why : String) (next : α → WG.M β) :
      ((invariant why : WG.M α) >>= next) = (invariant why : WG.M β) := rfl
  simp only [packetReceive,packetFront,bind_assoc,bind_if_source,pure_bind,bind_pure_unit,stopped]
  rfl

theorem source_factor (msg : List UInt8) (src : SkbSource) :
    wgReceive msg src = (do
      match ← front msg src with
      | none => pure ()
      | some ds => consumeData msg src ds) := by
  rw [wgReceive,packet_factor]
  simp only [front,bind_assoc,bind_if_source]

/-- The fields needed at the later admission cut, before any RX allocation. -/
def view (w : WGWorld) := (HolderEncrypt.fields w,Packets.snapshot w)

private theorem store {α : Type} {action : WG.M α} (ha : SameWGStore action) :
    SameView view action :=
  ha.of_factor (fun s : WGStoreView => view {dev:=s.dev,nlSock7:=s.nlSock7,nlSock8:=s.nlSock8}) view (fun _ => rfl)

private theorem append_view (msg src) : SameView view (modifyDev (appendHandshakeQueue msg src)) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a x v b run
  cases run
  unfold view HolderEncrypt.fields DecryptCarrier.decryptView carrierView keyView peerView rxView
  unfold keyWords currentCells stableView RxRing.nativeCell passiveView sendView handoffTxView
  unfold Packets.snapshot Packets.deviceStore
  cases hd : w.dev <;> simp [appendHandshakeQueue,hd,rxView]

private theorem cpu_view (cpu) : SameView view (modifyDev (setHandshakeCpu cpu)) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a x v b run
  cases run
  unfold view HolderEncrypt.fields DecryptCarrier.decryptView carrierView keyView peerView rxView
  unfold keyWords currentCells stableView RxRing.nativeCell passiveView sendView handoffTxView
  unfold Packets.snapshot Packets.deviceStore
  cases hd : w.dev <;> simp [setHandshakeCpu,hd,rxView]

private theorem cpumask_view : SameView view cpumaskNextOnline := by
  apply SameView.of_wp
  intro initial
  change Preserves (fun w => view w = initial) cpumaskNextOnline
  unfold cpumaskNextOnline
  simp only [branch]
  repeat' first
    | (rx_retention_head getDev; exact (store getDev_sameWGStore).wp (· = initial))
    | (rx_retention_head modifyDev; exact (cpu_view _).wp (· = initial))
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

macro "front_view_step " initial:term : tactic => `(tactic| first
  | (rx_retention_head getDev; exact (store getDev_sameWGStore).wp (· = $initial))
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | rx_retention_step)

theorem packet_view (msg src) : SameView view (packetFront msg src) := by
  apply SameView.of_wp
  intro initial
  change Preserves (fun w => view w = initial) (packetFront msg src)
  unfold packetFront
  simp only [branch,queueDeviceWork,invariant,unsupported]
  repeat' first
    | (rx_retention_head prepareSkbHeader; exact ((prepareSkbHeader_sameWGWorld _).factor view).wp (· = initial))
    | (rx_retention_head ipTunnelGetDsfield; exact ((ipTunnelGetDsfield_sameWGWorld _ _).factor view).wp (· = initial))
    | (rx_retention_head modifyDev; exact (append_view _ _).wp (· = initial))
    | (rx_retention_head cpumaskNextOnline; exact cpumask_view.wp (· = initial))
    | front_view_step initial

theorem front_view (msg src) : SameView view (front msg src) := by
  apply SameView.of_wp
  intro initial
  change Preserves (fun w => view w = initial) (front msg src)
  unfold front
  simp only [branch,unsupported]
  repeat' first
    | (rx_retention_head packetFront; exact (packet_view _ _).wp (· = initial))
    | front_view_step initial

/-- The actual front run selects either no data call or exactly one admission
outcome. Neither alternative assumes a funded output. -/
def Outcome (cs next : Ledger) (msg : List UInt8) (src : SkbSource)
    (w v : WGWorld) (a b : Ambient) : Prop :=
  ∃ choice u c, ((front msg src).run w).run a = .ok ((choice,u),c) ∧
    match choice with
    | none => next=cs ∧ v=u ∧ b=c
    | some ds => ∃ receipt, AdmissionOutcome.Outcome cs next msg src ds u v c b receipt

theorem front_boundary (hi : Boundary cs loans w)
    (run : ((front msg src).run w).run a=.ok ((choice,u),c)) : Boundary cs loans u :=
  HolderEncrypt.boundary_fields hi (congrArg Prod.fst
    ((ProjectedAction.iff_run_ambient _ _ _).mp (front_view msg src) w a choice u c run))

theorem front_packets (hi : Packets.Inv w)
    (run : ((front msg src).run w).run a=.ok ((choice,u),c)) : Packets.Inv u := by
  have same := congrArg Prod.snd
    ((ProjectedAction.iff_run_ambient _ _ _).mp (front_view msg src) w a choice u c run)
  unfold Packets.Inv at *
  change Packets.snapshot u = Packets.snapshot w at same
  rw [same]
  exact hi

theorem front_physical (hi : NativeRxInv epoch initial history w)
    (run : ((front msg src).run w).run a=.ok ((choice,u),c)) :
    NativeRxInv epoch initial history u := by
  have same := congrArg (fun x => x.1.1.2.1)
    ((ProjectedAction.iff_run_ambient _ _ _).mp (front_view msg src) w a choice u c run)
  obtain ⟨ring,refines,cell⟩ := hi
  exact ⟨ring,refines,same.trans cell⟩

/-- Normal returns select their next account from the actual source cut.
Header rejection and handshake queueing retain the old ledger; data admission
uses the existing exact enqueue/error-payment outcome. -/
theorem normal (hi : Boundary cs loans w) (fresh : Packets.Inv w)
    (physical : NativeRxInv epoch (PtrRing.init n) history w)
    (run : ((wgReceive msg src).run w).run a=.ok (((),v),b)) :
    ∃ next, Outcome cs next msg src w v a b ∧ Boundary next loans v := by
  rw [source_factor] at run
  simp only [StateT.run_bind] at run
  cases hf : ((front msg src).run w).run a with
  | error e => simp [hf] at run
  | ok out =>
    rcases out with ⟨⟨choice,u⟩,c⟩
    have account := front_boundary hi hf
    cases choice with
    | none =>
      simp only [hf,except_ok_bind,StateT.run_pure] at run
      obtain ⟨⟨_,rfl⟩,rfl⟩ := run
      exact ⟨cs,⟨none,_,_,hf,rfl,rfl,rfl⟩,account⟩
    | some ds =>
      simp only [hf,except_ok_bind] at run
      obtain ⟨holders,funded,stable⟩ := account
      obtain ⟨receipt,next,outcome,fundedOut,stableOut⟩ :=
        AdmissionOutcome.consume funded stable (front_packets fresh hf)
          (front_physical physical hf) c b run
      exact ⟨next,⟨some ds,u,c,hf,receipt,outcome⟩,holders,fundedOut,stableOut⟩

/-- The relation reconstructs the same complete normal native execution. -/
theorem Outcome.source (outcome : Outcome cs next msg src w v a b) :
    ((wgReceive msg src).run w).run a=.ok (((),v),b) := by
  obtain ⟨choice,u,c,frontRun,tail⟩ := outcome
  rw [source_factor]
  simp only [StateT.run_bind,frontRun,except_ok_bind]
  cases choice with
  | none => obtain ⟨_,rfl,rfl⟩ := tail; rfl
  | some ds => obtain ⟨receipt,certificate⟩ := tail; exact AdmissionOutcome.source certificate

/-- The incoming world fixes the admission cut and therefore the next ledger. -/
theorem Outcome.unique (left : Outcome cs next msg src w v a b)
    (right : Outcome cs other msg src w v a b) : next=other := by
  obtain ⟨choice,u,c,frontRun,tail⟩ := left
  obtain ⟨choice',u',c',frontRun',tail'⟩ := right
  rw [frontRun] at frontRun'
  obtain ⟨⟨rfl,rfl⟩,rfl⟩ := frontRun'
  cases choice with
  | none => exact tail.1.trans tail'.1.symm
  | some ds =>
    obtain ⟨receipt,certificate⟩ := tail
    obtain ⟨receipt',certificate'⟩ := tail'
    exact (AdmissionOutcome.unique certificate certificate').2

end Leanux.Proofs.WG.Queues.RxCredits.AdmissionReceive
