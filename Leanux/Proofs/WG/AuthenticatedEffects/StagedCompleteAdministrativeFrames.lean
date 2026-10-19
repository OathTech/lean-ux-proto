import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteOuterNativeFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteDumpClosed
import Leanux.Proofs.WG.Lifetimes.EnvControlsAudit
import Leanux.Proofs.Framing.Syscalls

/-! Native administrative frames use the packet and allocation projections.
MTU masks are justified field by field; routing wrappers keep their real calls. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct.Administrative
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal
set_option maxHeartbeats 600000

theorem native_socket (fd : Nat) (body : Leanux.M Int) (h : List Event)
    (checked : Preserves (Carrier h) body) : Preserves (Carrier h) (Leanux.socketCallOn fd body) := by
  have files {α : Type} (a : FS.M α) : Preserves (Carrier h) (monadLift a : Leanux.M α) :=
    native_of_checked (fs a) h
  routing_tx_source [Leanux.socketCallOn] using [checked,files]

theorem native_rtnetlink (body : Leanux.M Int) (h : List Event)
    (checked : Preserves (Carrier h) body) : Preserves (Carrier h) (Leanux.rtnetlinkRequest body) := by
  have files {α : Type} (a : FS.M α) : Preserves (Carrier h) (monadLift a : Leanux.M α) :=
    native_of_checked (fs a) h
  have tasks {α : Type} (a : TaskM α) : Preserves (Carrier h) (monadLift a : Leanux.M α) :=
    native_of_checked (fs (monadLift a : FS.M α)) h
  have effects {α : Type} (a : AmbientM α) := native_of_checked (ambient a) h
  have read := native_of_checked CompleteProduct.read h
  have edit (f : World → World) (same : ∀ w, wgStoreView (f w).wg = wgStoreView w.wg) :=
    native_of_checked (CompleteProduct.edit f same) h
  routing_tx_source [Leanux.rtnetlinkRequest,Leanux.socketCallOn,skipCut,unsupported]
    using [checked,files,tasks,effects,read]
  all_goals exact edit _ (fun _ => rfl)

theorem add_route (dst plen oif typeCode metric mtu nlflags : Nat) (h : List Event) :
    Preserves (Carrier h) (Env.wgAddroute dst plen oif typeCode metric mtu nlflags) := by
  have routes {α : Type} (a : Net.M α) := native_of_checked (routing a) h
  have effects {α : Type} (a : AmbientM α) := native_of_checked (ambient a) h
  routing_tx_source [Env.wgAddroute,invariant] using [routes,effects]

theorem add_addr (addr plen : Nat) (h : List Event) :
    Preserves (Carrier h) (Env.wgAddaddr addr plen) := by
  have read := native_of_checked wg_read h
  have routes {α : Type} (a : Net.M α) := native_of_checked (routing a) h
  have effects {α : Type} (a : AmbientM α) := native_of_checked (ambient a) h
  routing_tx_source [Env.wgAddaddr,getRouting,modifyRouting,unsupported] using [read,routes,effects]

theorem del_route (family : Nat) (named : Bool) (dst plen oif typeCode metric : Nat) (h : List Event) :
    Preserves (Carrier h) (Env.wgDelroute family named dst plen oif typeCode metric) := by
  have read := native_of_checked wg_read h
  have routes {α : Type} (a : Net.M α) := native_of_checked (routing a) h
  have effects {α : Type} (a : AmbientM α) := native_of_checked (ambient a) h
  routing_tx_source [Env.wgDelroute,getRouting,modifyRouting,unsupported] using [read,routes,effects]

theorem mtu (value : Nat) : Checked (liftPrefix (Env.setMtu value)) := by
  have framed : SameView (fun w : World => StagedEntry.view w.wg) (Env.setMtu value) :=
    (setMtu_sameEnvScalar value).of_factor
      (fun s : ProductStore43 => StagedEntry.view {dev := s.2.2.2.dev}) _ (fun w => by
        cases device : w.wg.dev <;>
          simp [funext_iff,StagedEntry.view,envScalarView,envScalarStore,envScalarDevice,
            productStoreView,wgStoreView,Packets.epoch,Staged.stagedAt,PacketMaterial.view,
            TxDisposition.txPackets,Packets.snapshot,Packets.deviceStore,txQueueContents,
            RxCredits.handoffTxView,device])
  apply CompleteProduct.native
  intro h
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  obtain ⟨⟨ledger,entry⟩,history,allocated⟩ := before
  have same := envScalar_identity_metadata w v
    ((ProjectedAction.iff_run _ _ _).mp (setMtu_sameEnvScalar value) w result v run)
  exact ⟨⟨ledger,entry.same_view ((ProjectedAction.iff_run _ _ _).mp framed w result v run)⟩,
    history,allocated.congr (congrArg Prod.fst same) (congrArg Prod.snd same)⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct.Administrative
