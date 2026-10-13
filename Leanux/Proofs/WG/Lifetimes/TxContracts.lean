import Leanux.Proofs.WG.Lifetimes.TxAccess
import Leanux.Proofs.Logged.PrefixLoops

/-! The extra actual TX primitives and device updates needed by staging.
Device contracts retain arbitrary cached identity predicates; they are not
inferred from identity equality for an arbitrary ambient invariant. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

inductive TxDeviceUpdate where
  | cpu (cpu : Int)
  | ring (item : List SkbId)
  | work (pid : PeerId)
  | handshake (pid : PeerId)
  | dropped (count : Nat)

def TxDeviceUpdate.apply : TxDeviceUpdate → Device → Device
  | .cpu n, d => {d with encryptLastCpu := n}
  | .ring item, d => {d with encryptQueue := d.encryptQueue.produce item}
  | .work pid, d => {d with txWorkQueue := d.txWorkQueue ++ [pid]}
  | .handshake pid, d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]}
  | .dropped count, d => {d with txDropped := d.txDropped + count}

structure TxContracts (I : List LifetimeEvent → World → Prop) : Prop where
  get : ∀ P id, AmbientSpec I P (getTxSkbPrefix id) (fun _ => P)
  set : ∀ P id f, AmbientSpec I P (setTxSkbPrefix id f) (fun _ => P)
  put : ∀ kp now, PrefixPreserves I LifetimeEvent.Safe (keypairPutPrefix kp now)
  free : ∀ id, PrefixPreserves I LifetimeEvent.Safe (freeTxSkbPrefix id)
  alloc : ∀ p, PrefixPreserves I LifetimeEvent.Safe (newTxSkbPrefix p)
  device : ∀ P (update : TxDeviceUpdate), AmbientSpec I P (liftPrefix (modifyDev update.apply)) (fun _ => P)

theorem txDeviceUpdate_allocation (P : IdentityView → Prop) (u : TxDeviceUpdate) :
    AmbientSpec AllocationInv P (liftPrefix (modifyDev u.apply)) (fun _ => P) := by
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.1.safe)
  intro h w x v hi hr
  have hf : (identityView v, allocationMetadata v) = (identityView w, allocationMetadata w) := by
    cases hr
    cases u <;> unfold identityView Peers.snapshot keypairResidents packetResidents allocationMetadata <;>
      simp [TxDeviceUpdate.apply, Option.bind_map, Function.comp_def, deviceAllocationMetadata] <;> rfl
  have he : identityView v = identityView w := congrArg Prod.fst hf
  exact ⟨hi.1.congr he (congrArg Prod.snd hf), he ▸ hi.2⟩

theorem allocationTx : TxContracts AllocationInv where
  get := getTxSkbPrefix_allocation
  set := setTxSkbPrefix_allocation
  put := keypairPutPrefix_allocation
  free := freeTxSkbPrefix_allocation
  alloc := fun p => PacketAllocation.preserves (.tx p)
  device := txDeviceUpdate_allocation

end Leanux.Proofs.WG.Lifetimes
