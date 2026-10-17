import Leanux.Proofs.WG.Roaming.PublicationSource
import Leanux.Proofs.WG.Roaming.Authentication

/-! The native decryption read is connected to actual product execution.
Public publication predicates use the Product snapshot, and the suffix keeps
arbitrary product callbacks. No whole-step authentication claim is made here. -/
set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem decryptPacket_key_present (pkt : RxPacket) (g final : WGWorld)
    (ambient after : Ambient) (result : Option RxPacket)
    (run : ((decryptPacket pkt).run g).run ambient = .ok ((result, final), after)) :
    ∃ key, (g.dev.bind fun d => d.keypairs[pkt.keypair]?) = some key := by
  cases hd : g.dev with
  | none =>
    simp [decryptPacket, getKeypair, getDev, branch, AmbientM.branch, invariant,
      AmbientM.invariant, StateT.run_bind, hd] at run
    cases run
  | some d =>
    cases hk : d.keypairs[pkt.keypair]? with
    | none =>
      simp [decryptPacket, getKeypair, getDev, branch, AmbientM.branch, invariant,
        AmbientM.invariant, StateT.run_bind, StateT.run_pure, hd, hk] at run
      cases run
    | some key => exact ⟨key, by simp [hk]⟩

theorem decryptPacket_authentication_at (pkt : RxPacket) (before : Campaign2.Product.Snapshot) :
    Campaign2.Product.Ensures (liftWG (decryptPacket pkt)) (fun s => s = before)
      (fun result _ => ∀ plain, result = some plain → ∃ key,
        keyAt before pkt.keypair = some key ∧
        plain.source = pkt.source ∧ plain.peer = pkt.peer ∧ plain.keypair = pkt.keypair ∧
        plain.nonce = u64le pkt.bytes 8 ∧
        aeadDecrypt key.receiving.key (counterNonce (u64le pkt.bytes 8))
          (pkt.bytes.drop 16) [] = some plain.bytes) := by
  intro w result final pre run plain same
  change (((decryptPacket pkt).run w.wg).run w.ambient >>= fun ((value, g), ambient) =>
    Except.ok (value, {w with wg := g, ambient})) = _ at run
  cases native : ((decryptPacket pkt).run w.wg).run w.ambient with
  | error error => rw [native] at run; cases run
  | ok out =>
    rcases out with ⟨⟨value, g⟩, ambient⟩
    rw [native] at run
    cases run
    obtain ⟨key, resident⟩ := decryptPacket_key_present pkt w.wg g w.ambient ambient result native
    refine ⟨key, ?_, decryptPacket_authenticated pkt key w.wg w.ambient result g ambient
      resident native plain same⟩
    subst before
    exact resident

theorem setRxSkb_plain (id : SkbId) (plain : RxPacket) :
    ⦃fun _ => ⌜True⌝⦄ liftWG (setRxSkb id (fun _ => plain))
      ⦃⇓? _ w => ⌜packetAt (Campaign2.Product.snapshot w) id = some plain⌝⦄ := by
  apply (Noise.Product.ensures_iff _ _ _).mp
  intro w result final pre run
  change (((setRxSkb id (fun _ => plain)).run w.wg).run w.ambient >>=
    fun ((value, g), ambient) => Except.ok (value, {w with wg := g, ambient})) = _ at run
  cases hd : w.wg.dev with
  | none =>
    simp [setRxSkb, liftSkb, getDev, hd, invariant, AmbientM.invariant] at run
    cases run
  | some d =>
    cases hp : d.rxSkbs[id]? with
    | none =>
      simp [setRxSkb, liftSkb, getDev, hd, SkbStore.setRx, SkbStore.getRx, hp,
        invariant, AmbientM.invariant] at run
      cases run
    | some p =>
      simp [setRxSkb, liftSkb, getDev, hd, SkbStore.setRx, SkbStore.getRx, hp, modifyDev] at run
      rcases run with ⟨rfl, rfl⟩
      simp [packetAt, Campaign2.Product.snapshot, Campaign2.snapshot, Campaign2.core]

theorem publicationSuffix_result (softirq irqExit : Leanux.M Unit) (cut : Option PublicationCut) :
    Campaign2.Product.Ensures (publicationSuffix softirq irqExit cut) (fun _ => True)
      (fun result _ => result = cut.isSome) := by
  have hany {α : Type} (a : Leanux.M α) :
      Noise.Product.Ensures a (fun _ => True) (fun _ _ => True) :=
    (Noise.Product.ensures_iff _ _ _).mpr (unconstrained_prefix a)
  change Noise.Product.Ensures _ _ _
  cases cut with
  | none =>
    intro w result final pre run
    cases run
    rfl
  | some cut =>
    unfold publicationSuffix
    refine Noise.Product.ensures_bind _ _ (hany _) ?_
    intro _
    refine Noise.Product.ensures_bind _ _ (hany _) ?_
    intro _
    refine Noise.Product.ensures_bind _ _ (hany _) ?_
    intro _ w result final pre run
    cases run
    rfl

end Leanux.Proofs.WG.Roaming
