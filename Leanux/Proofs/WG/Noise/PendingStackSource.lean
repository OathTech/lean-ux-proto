import Leanux.Proofs.WG.Noise.PendingStackFrames

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Noise.PendingStack
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues PendingReception

/-- The actual transmit, including negative status paths and final peerPut,
preserves the pending-ticket invariant and its configured/slot support. -/
theorem wgXmit_native (family addr : Nat) (packets : List Packet) (mtu : Nat) (seen : List Nat) :
    Preserves (fun w => PendingSession.NativeInv w seen) (wgXmit family addr packets mtu) := by
  let P := fun w => PendingSession.NativeInv w seen
  have getPeerRule (pid : PeerId) : Preserves P (getPeer pid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient p v after hi run
    exact (getPeer_normal pid w v p ambient after run).1 ▸ hi
  have lookup : Preserves P (lookupDst family addr) := lookupDst_native family addr seen
  have trim (pid : PeerId) : Preserves P (xmitTrim pid) := xmitTrim_native pid seen
  have splice (pid : PeerId) (packets : List Packet) : Preserves P (xmitSplice pid packets) :=
    xmitSplice_native pid packets seen
  have stage (pid : PeerId) : Preserves P (sendStagedPackets pid) := staged_native pid seen
  have pay (pid : Option PeerId) : Preserves P (peerPut pid) := PendingReception.pay pid seen
  have loopback (sites : List HiddenSite) (raised : Bool) : Preserves P (loopbackSend sites raised) :=
    native_store _ (loopbackSend_kernel sites raised) seen
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have routing {α : Type} (a : Net.M α) : Preserves P (monadLift a : WG.M α) :=
    native_store _ (liftRouting_sameWGStore a) seen
  have errors : Preserves P (modifyDev fun d => {d with txErrors := d.txErrors+1}) :=
    native_modifyDevice (fun d => {d with txErrors := d.txErrors+1})
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) seen
  have loop {α β : Type} (xs : List α) (init : β) (f : α → β → WG.M (ForInStep β))
      (hf : ∀x b, Preserves P (f x b)) : Preserves P (forIn xs init f) :=
    list_view_spec id P xs init f hf
  rw [wgXmitSource_eq]
  rxstack_preserves_source [wgXmitSource,WG.andM,branch,invariant,skipCutSites,envOk]
    using [getPeerRule,lookup,trim,splice,stage,pay,loopback,ambient,routing,errors,loop]


/-- The generic C1 Stack source is instantiated only with the actual original
transmit call. Empty observations are used solely to reuse source composition. -/
def transmit (family addr : Nat) (packets : List Packet) (mtu : Nat) : PrefixM Empty Int :=
  liftPrefix (liftWG (wgXmit family addr packets mtu))

def stackSource (bytes : List UInt8) : PrefixM Empty Unit :=
  stackReceiveWith (receive4With (reply4With transmit)) bytes

private theorem empty_history (h : List Empty) : h = [] := by
  cases h with
  | nil => rfl
  | cons e rest => cases e

theorem transmit_projects (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    ProjectsPrefix (fun _ : LifetimeEvent => (none : Option Empty)) id
      (liftWGObserver (wgXmitPrefix family addr packets mtu))
      (transmit family addr packets mtu) := by
  intro w h
  have erased := liftWGObserver_erases (wgXmitPrefix_erases family addr packets mtu) w h
  simp only [transmit,runPrefix_lift,empty_history,erased]
  cases (liftWG (wgXmit family addr packets mtu)).run w <;> rfl

theorem stackSource_projects (bytes : List UInt8) :
    ProjectsPrefix (fun _ : LifetimeEvent => (none : Option Empty)) id
      (stackReceivePrefix bytes) (stackSource bytes) := by
  rw [stackReceivePrefix_factor]
  unfold stackSource
  apply stackReceiveWith_projects
  intro packet
  rw [receive4Prefix_factor]
  apply receive4With_projects
  intro dst packet
  rw [reply4Prefix_factor]
  exact reply4With_projects _ _ _ transmit_projects dst packet

/-- Exact original outcome, including every Stop; this is not a successful-run
or replacement-callback premise. -/
theorem stackSource_erases (bytes : List UInt8) :
    ErasesPrefix (stackSource bytes) (Env.deliverInner bytes) := by
  intro w h
  rw [empty_history h]
  have project := congrArg Prod.fst (stackSource_projects bytes w [])
  have original := stackReceivePrefix_erases bytes w []
  simp only [List.filterMap_nil] at project
  rw [original] at project
  have map_identity (value : Except Stop (Unit × World)) :
      value.map (fun x => (id x.1,x.2)) = value := by
    cases value <;> rfl
  exact project.trans (map_identity _)

theorem stackSource_preserves (seen : List Nat) (bytes : List UInt8) :
    PrefixPreserves (fun (_ : List Empty) (w : World) => PendingSession.NativeInv w.wg seen)
      (fun _ => True) (stackSource bytes) := by
  have safe : ∀ (_ : List Empty) (w : World), PendingSession.NativeInv w.wg seen → True :=
    fun _ _ _ => True.intro
  have store : ∀ (_ : List Empty) (w v : World), productStoreView v = productStoreView w →
      PendingSession.NativeInv w.wg seen → PendingSession.NativeInv v.wg seen := by
    intro h w v same hi
    exact PendingSession.native_store w.wg v.wg seen
      (congrArg (fun s : ProductStore43 => s.2.2.2) same) hi
  unfold stackSource
  apply stackReceiveWith_preserves safe store
  intro packet
  apply receive4With_preserves safe store
  intro dst packet
  apply reply4With_preserves safe store
  intro family addr packets mtu
  unfold transmit
  apply PrefixEnsures.lift (Q := fun _ _ w => PendingSession.NativeInv w.wg seen) _ safe
  intro h w result v hi run
  exact (hoare_iff_run _ _ _).mp
    (PendingSession.native_product _ (wgXmit_native family addr packets mtu) seen)
    w result v hi run

/-- The complete original Stack callback, including routed IPv4 replies back
through wgXmit and all IPv4/IPv6 refusal paths, transports NativeInv. -/
theorem deliverInner_native (seen : List Nat) (bytes : List UInt8) :
    Preserves (fun w : World => PendingSession.NativeInv w.wg seen)
      (Env.deliverInner bytes) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi run
  obtain ⟨suffix,appended,safe,normal⟩ := stackSource_preserves seen bytes w [] hi
  have erased := (stackSource_erases bytes w []).trans run
  simpa only [erased] using normal

end Leanux.Proofs.WG.Noise.PendingStack
