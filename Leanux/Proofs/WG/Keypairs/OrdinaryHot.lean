import Leanux.Proofs.WG.Keypairs.Ordinary
import Leanux.Proofs.Framing.WGTime
import Leanux.Proofs.Framing.WGHandshake

set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Keypairs
open Leanux Leanux.WG Std.Do Leanux.Proofs.Framing Leanux.Proofs.Framing.Allocation

theorem deriveKeys_sameSnapshot (kp : KeypairId) (initiator : Bool) (chainingKey : List UInt8) :
    SameSnapshot (deriveKeys kp initiator chainingKey) := by
  apply sameSnapshot_of_wp
  intro s
  have clock_spec : Hoare (hiddenClock64 .deriveKeysBirthdate : WG.M Int64)
      (fun w => snapshot w = s) (fun _ w => snapshot w = s) :=
    hoare_liftAmbient (AmbientM.hiddenClock64 .deriveKeysBirthdate) (fun w => snapshot w = s)
  unfold Hoare at clock_spec
  have kdf_spec := (kdf_sameWGWorld true false chainingKey []).wp (fun w => snapshot w = s)
  have out_spec := fun outs i => (kdfOut_sameWGWorld outs i).wp (fun w => snapshot w = s)
  mvcgen [deriveKeys, clock_spec, kdf_spec, out_spec,
    getKeypair, getDev, setKeypair, modifyDev, invariant, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [snapshot]
  all_goals try subst s
  all_goals
    split
    all_goals
      calc
        _ = _ := by apply mapSnapshot_insert_same <;> first | assumption | rfl
        _ = _ := by assumption

theorem getKeypair_snapshot_wp (i : Nat) (P : Snapshot → Prop) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ getKeypair i
    ⦃⇓? k w => ⌜P (snapshot w) ∧ (snapshot w).slots i = some (cell k)⌝⦄ := by
  mvcgen [getKeypair, getDev, invariant, AmbientM.invariant]
  all_goals simp_all [snapshot]

theorem setKeypair_snapshot_wp (i : Nat) (k : Keypair) (P : Snapshot → Prop) :
    ⦃fun w => ⌜P (snapshot w) ∧ (snapshot w).slots i = some (cell k)⌝⦄ setKeypair i k
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x w' ambient' hp hr
  cases hd : w.dev with
  | none => simp [snapshot, hd] at hp
  | some d =>
    have hs : ((setKeypair i k).run w).run ambient =
        .ok (((), Leanux.Proofs.WG.CounterWindow.store w i k), ambient) := rfl
    rw [hs] at hr
    cases hr
    rw [snapshot_store w d i k hd, put_existing _ _ _ hp.2]
    exact hp.1

theorem decryptPacket_sameSnapshot (pkt : RxPacket) : SameSnapshot (decryptPacket pkt) := by
  apply sameSnapshot_of_wp
  intro s
  have birthday_spec := fun d birth seconds f =>
    (branchExpired_sameWGWorld d birth seconds f).wp (fun w => snapshot w = s)
  have alloc_spec : Hoare (hiddenAlloc .skbCowDataRx : WG.M Bool)
      (fun w => snapshot w = s) (fun _ w => snapshot w = s) :=
    hoare_liftAmbient (AmbientM.hiddenAlloc .skbCowDataRx) (fun w => snapshot w = s)
  unfold Hoare at alloc_spec
  have get_spec := fun i => getKeypair_snapshot_wp i (fun t => t = s)
  have set_spec := fun i k => setKeypair_snapshot_wp i k (fun t => t = s)
  mvcgen [decryptPacket, birthday_spec, alloc_spec, Leanux.WG.orM,
    branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
    get_spec, set_spec, invariant, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [snapshot, cell]

end Leanux.Proofs.WG.Keypairs
