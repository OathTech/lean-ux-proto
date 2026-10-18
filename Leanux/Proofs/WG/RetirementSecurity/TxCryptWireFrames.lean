import Leanux.Proofs.WG.RetirementSecurity.TxCryptDisposal

/-! The completion path changes endpoint/timer/work bookkeeping, but not
the encryption ring or any stored TX packet. Queue ownership is framed by
the existing concrete completion theorem, separately from these fields. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

def txCryptWire (w : WGWorld) := (Queues.TxRing.nativeCell w,fun id => Queues.TxDisposition.txPackets w id)

theorem cryptWire_store {action : WG.M α} (same : SameWGStore action) :
    SameView txCryptWire action :=
  same.of_factor (fun store => txCryptWire {dev := store.dev}) txCryptWire (fun _ => rfl)

private theorem wire_modify (initial) (f : Device → Device)
    (epoch : ∀ d, (f d).ifindex = d.ifindex)
    (ring : ∀ d, (f d).encryptQueue = d.encryptQueue)
    (packets : ∀ d, (f d).txSkbs = d.txSkbs) :
    Preserves (fun w => txCryptWire w = initial) (modifyDev f) := by
  apply hoare_modify
  intro w before
  simpa only [txCryptWire,Queues.TxRing.nativeCell,Queues.TxDisposition.txPackets,
    Option.map_map,Option.bind_map,Function.comp_def,epoch,ring,packets] using before

macro "crypt_wire_step " initial:term : tactic => `(tactic| first
  | rxstack_preserves_join
  | (rx_retention_head getPeer; exact getPeer_preserves _ _)
  | (rx_retention_head getDev; exact (cryptWire_store getDev_sameWGStore).wp (fun s => s = $initial))
  | (rx_retention_head getKeypair
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a k v b before run
     exact (KeyTimes.getKeypair_return _ w v k a b run).1 ▸ before)
  | (rx_retention_head getTxSkb
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a k v b before run
     exact (Packets.getTxSkb_current _ w v k a b run).1 ▸ before)
  | (rx_retention_head setPeer; unfold setPeer)
  | (rx_retention_head setKeypair; unfold setKeypair)
  | (rx_retention_head modifyDev; apply wire_modify $initial; all_goals intro d; rfl)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (allocation_release_lift_from Net.M; exact hoare_liftRouting _ _ (fun _ _ h => h))
  | (rx_retention_head liftRouting; exact hoare_liftRouting _ _ (fun _ _ h => h))
  | (rx_retention_head getRouting
     exact hoare_liftRouting ((fun (s : Net.State) => s.toRouting) <$> (get : Net.M Net.State))
       _ (fun _ _ h => h))
  | (rx_retention_head get
     exact hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2))
  | (rx_retention_head MonadStateOf.get
     exact hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2))
  | (rx_retention_head throw
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a result v b before run
     cases run)
  | (rx_retention_head MonadExceptOf.throw
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a result v b before run
     cases run)
  | (rx_retention_head modify; apply hoare_modify; intro w before; exact before)
  | rx_retention_step)

end Leanux.Proofs.WG.RetirementSecurity
