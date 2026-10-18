import Leanux.Proofs.WG.RetirementSecurity.StackOwnership
import Leanux.Proofs.WG.RetirementSecurity.RxConsumeHolders
import Leanux.Proofs.WG.Lifetimes.ReceiveIngress

/-! Original UDP receive retains the concrete key account. Its transport
allocation bound comes from campaign 1's actual observer; handshake queue and
header work are passive for key holders. No authenticated-receive premise is
needed for this ownership statement. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues
open StackOwnership

theorem Allocated.native {observer : MixedM α} {native : WG.M α}
    (erases : ErasesStatePrefix observer native)
    (keeps : StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe observer)
    (before : Allocated w) (a b : Ambient)
    (run : (native.run w).run a = .ok ((result,v),b)) : Allocated v := by
  obtain ⟨history,account⟩ := before
  obtain ⟨_,_,_,post⟩ := keeps w a history account
  have observed := erases w a history
  rw [run] at observed
  rw [observed] at post
  exact ⟨_,post⟩

namespace ReceiveEntry
abbrev Ready (temporary : Credits.Ledger) (w : WGWorld) := HolderAccount temporary w ∧ Allocated w

theorem store {action : WG.M α} (same : SameWGStore action) : Preserves (Ready temporary) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have shape := (ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run
  exact ⟨before.1.points ((ProjectedAction.iff_run_ambient _ _ _).mp
    (ownershipPoints_kernel _ same) w a result v b run),before.2.store shape⟩

theorem consume (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    Preserves (Ready temporary) (consumeData msg src ds) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases result
  exact ⟨before.1.consume_data before.2.bounded msg src ds a b run,
    Allocated.native (consumeDataPrefix_erases msg src ds)
      (consumeDataPrefix_allocation msg src ds) before.2 a b run⟩

theorem append (msg : List UInt8) (src : SkbSource) :
    Preserves (Ready temporary) (modifyDev fun d => {d with handshakeQueue := d.handshakeQueue.produce (msg,src), handshakeQueueLen := d.handshakeQueueLen + 1}) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact ⟨before.1.points ((ProjectedAction.iff_run_ambient _ _ _).mp
      (ownership_modifyDev (appendHandshakeQueue msg src) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)) w a result v b run),
    Allocated.native (erasesStatePrefix_lift _)
      (allocationReceiveIngress.append msg src) before.2 a b run⟩

theorem cpu (number : Int) : Preserves (Ready temporary) (modifyDev fun d => {d with handshakeLastCpu := number}) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact ⟨before.1.points ((ProjectedAction.iff_run_ambient _ _ _).mp
      (ownership_modifyDev (setHandshakeCpu number) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)) w a result v b run),
    Allocated.native (erasesStatePrefix_lift _)
      (allocationReceiveIngress.cpu number) before.2 a b run⟩

theorem cpu_next : Preserves (Ready temporary) cpumaskNextOnline := by
  have device := store (temporary := temporary) getDev_sameWGStore
  have changeCpu := cpu (temporary := temporary)
  have ambient {α : Type} (a : AmbientM α) : Preserves (Ready temporary) (monadLift a : WG.M α) :=
    hoare_liftAmbient a _
  rxstack_preserves_source [cpumaskNextOnline,branch] using [device,changeCpu,ambient]

theorem packet (msg : List UInt8) (src : SkbSource) : Preserves (Ready temporary) (packetReceive msg src) := by
  have header := store (temporary := temporary) ((prepareSkbHeader_sameWGWorld msg).factor wgStoreView)
  have ds (protocol : Nat) (bytes : List UInt8) :=
    store (temporary := temporary) ((ipTunnelGetDsfield_sameWGWorld protocol bytes).factor wgStoreView)
  have device := store (temporary := temporary) getDev_sameWGStore
  have add := append (temporary := temporary) msg src
  have data := consume (temporary := temporary) msg src
  have cpu := cpu_next (temporary := temporary)
  have ambient {α : Type} (a : AmbientM α) : Preserves (Ready temporary) (monadLift a : WG.M α) :=
    hoare_liftAmbient a _
  rxstack_preserves_source [packetReceive,branch,invariant,unsupported,queueDeviceWork]
    using [header,ds,device,add,data,cpu,ambient]

theorem receive (msg : List UInt8) (src : SkbSource) : Preserves (Ready temporary) (wgReceive msg src) := by
  have packet := packet (temporary := temporary) msg src
  have ambient {α : Type} (a : AmbientM α) : Preserves (Ready temporary) (monadLift a : WG.M α) :=
    hoare_liftAmbient a _
  rxstack_preserves_source [wgReceive,branch,unsupported] using [packet,ambient]

end ReceiveEntry
end Leanux.Proofs.WG.RetirementSecurity
