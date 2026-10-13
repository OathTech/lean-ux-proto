import Leanux.Proofs.WG.Keypairs.Ordinary
import Leanux.Proofs.Framing.WGTime
import Leanux.Proofs.Framing.WGHandshake

set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Keypairs
open Leanux Leanux.WG Std.Do Leanux.Proofs.Framing Leanux.Proofs.Framing.Allocation

/-- Compatibility names for the shared original-effect contracts. -/
theorem hiddenAlloc_sameKernel (site : AllocSite) : SameKernel (hiddenAlloc site) :=
  Framing.hiddenAlloc_sameKernel site

theorem hiddenClock_sameKernel (site : HiddenSite) : SameKernel (hiddenClock site) :=
  Framing.hiddenClock_sameKernel site

theorem birthdateHasExpired_sameKernel (birthday : Int64) (seconds : Nat) :
    SameKernel (birthdateHasExpired birthday seconds) :=
  Framing.birthdateHasExpired_sameKernel birthday seconds

theorem kdf_sameKernel (second third : Bool) (chainingKey data : List UInt8) :
    SameKernel (kdf second third chainingKey data) :=
  Framing.kdf_sameKernel second third chainingKey data

theorem kdfOut_sameKernel (outs : List (List UInt8)) (i : Nat) :
    SameKernel (kdfOut outs i) :=
  Framing.kdfOut_sameKernel outs i

theorem deriveKeys_sameSnapshot (kp : KeypairId) (initiator : Bool) (chainingKey : List UInt8) :
    SameSnapshot (deriveKeys kp initiator chainingKey) := by
  apply sameSnapshot_of_wp
  intro s
  have clock_spec := (sameSnapshot_of_sameKernel (Framing.hiddenClock64_sameKernel .deriveKeysBirthdate)).wp (fun t => t = s)
  have kdf_spec := (sameSnapshot_of_sameKernel (kdf_sameKernel true false chainingKey [])).wp (fun t => t = s)
  have out_spec := fun outs i => (sameSnapshot_of_sameKernel (kdfOut_sameKernel outs i)).wp (fun t => t = s)
  mvcgen [deriveKeys, clock_spec, kdf_spec, out_spec,
    getKeypair, getDev, getK, setKeypair, modifyDev, modifyK, invariant]
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
  mvcgen [getKeypair, getDev, getK, invariant]
  all_goals simp_all [snapshot]

theorem setKeypair_snapshot_wp (i : Nat) (k : Keypair) (P : Snapshot → Prop) :
    ⦃fun w => ⌜P (snapshot w) ∧ (snapshot w).slots i = some (cell k)⌝⦄ setKeypair i k
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x w' hp hr
  cases hd : w.k.wg with
  | none => simp [snapshot, hd] at hp
  | some d =>
    have hs : (setKeypair i k).run w = .ok ((), Leanux.Proofs.WG.CounterWindow.store w i k) := rfl
    rw [hs] at hr
    cases hr
    rw [snapshot_store w d i k hd, put_existing _ _ _ hp.2]
    exact hp.1

theorem decryptPacket_sameSnapshot (pkt : RxPacket) : SameSnapshot (decryptPacket pkt) := by
  apply sameSnapshot_of_wp
  intro s
  have birthday_spec := fun d birth seconds f =>
    (sameSnapshot_of_sameKernel (Framing.branchExpired_sameKernel d birth seconds f)).wp (fun t => t = s)
  have alloc_spec := (sameSnapshot_of_sameKernel (hiddenAlloc_sameKernel .skbCowDataRx)).wp (fun t => t = s)
  have get_spec := fun i => getKeypair_snapshot_wp i (fun t => t = s)
  have set_spec := fun i k => setKeypair_snapshot_wp i k (fun t => t = s)
  mvcgen [decryptPacket, birthday_spec, alloc_spec, Leanux.WG.orM, branch, branchCmp,
    get_spec, set_spec, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [snapshot, cell]

end Leanux.Proofs.WG.Keypairs
