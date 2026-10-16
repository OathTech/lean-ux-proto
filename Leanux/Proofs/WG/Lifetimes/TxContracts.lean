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

structure TxContracts (I : List LifetimeEvent → WGWorld → Prop) : Prop where
  get : ∀ P id, AmbientSpec I P (getTxSkbPrefix id) (fun _ => P)
  set : ∀ P id f, AmbientSpec I P (setTxSkbPrefix id f) (fun _ => P)
  put : ∀ kp now, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (keypairPutPrefix kp now)
  free : ∀ id, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (freeTxSkbPrefix id)
  alloc : ∀ p, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (newTxSkbPrefix p)
  device : ∀ P (update : TxDeviceUpdate), AmbientSpec I P (liftWGPrefix (modifyDev update.apply)) (fun _ => P)

theorem txDeviceUpdate_allocation (P : IdentityView → Prop) (u : TxDeviceUpdate) :
    AmbientSpec AllocationInv P (liftWGPrefix (modifyDev u.apply)) (fun _ => P) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1.safe)
  intro h w ambient x v ambient' hi hr
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


/-- The original product invariant domain, with native leaves executed by the
actual runner adapter. No condition restricts I to WireGuard observations. -/
structure ProductTxContracts (I : List LifetimeEvent → World → Prop) : Prop where
  get : ∀ P id, ProductAmbientSpec I P (liftWGObserver (getTxSkbPrefix id)) (fun _ => P)
  set : ∀ P id f, ProductAmbientSpec I P (liftWGObserver (setTxSkbPrefix id f)) (fun _ => P)
  put : ∀ kp now, PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (keypairPutPrefix kp now))
  free : ∀ id, PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (freeTxSkbPrefix id))
  alloc : ∀ p, PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (newTxSkbPrefix p))
  device : ∀ P (update : TxDeviceUpdate),
    ProductAmbientSpec I P (liftWGObserver (liftWGPrefix (modifyDev update.apply))) (fun _ => P)

theorem ProductTxContracts.ofNative (t : TxContracts I) :
    ProductTxContracts (fun h w => I h w.wg) where
  get := fun P id => (t.get P id).liftWGObserver
  set := fun P id f => (t.set P id f).liftWGObserver
  put := fun kp now => (t.put kp now).liftWGObserver
  free := fun id => (t.free id).liftWGObserver
  alloc := fun p => (t.alloc p).liftWGObserver
  device := fun P update => (t.device P update).liftWGObserver

end Leanux.Proofs.WG.Lifetimes
