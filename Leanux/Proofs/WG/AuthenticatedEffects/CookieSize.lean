import Leanux.Proofs.WG.AuthenticatedEffects.CryptoSizes
import Leanux.Proofs.WG.AuthenticatedEffects.SentFrames

/-! Byte-width contracts derived from the actual source computations. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do

private theorem anyWG (action : WG.M α) : Hoare action (fun _ => True) (fun _ _ => True) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intros
  trivial

private theorem anyAmbient (action : AmbientM α) : Hoare action (fun _ => True) (fun _ _ => True) := by
  apply (hoare_iff_run _ _ _).mpr
  intros
  trivial

theorem makeCookie_size_spec (src : SkbSource) :
    Hoare (makeCookie src) (fun _ => True) (fun bytes _ => bytes.length = 16) := by
  have digest (secret addr : List UInt8) : Hoare
      (pure (blake2s 16 secret (addr ++ netBytes src.sport 2)) : WG.M (List UInt8))
      (fun _ => True) (fun bytes _ => bytes.length = 16) := by
    apply hoare_consequence (hoare_pure _ (fun _ => True)) (fun _ _ => trivial)
    intro bytes w h
    rcases h with ⟨rfl,_⟩
    exact blake2s_sixteen_length _ _
  have tail : Hoare (do
      let secret := (← getDev).cookieSecret
      let addr ← do
        if ← branch .cookieProtoIp (src.family == 4) then pure (netBytes src.saddr 4)
        else if ← branch .cookieProtoIpv6 (src.family == 6) then pure (netBytes src.saddr 16)
        else pure []
      return blake2s 16 secret (addr ++ netBytes src.sport 2) : WG.M (List UInt8))
      (fun _ => True) (fun bytes _ => bytes.length = 16) := by
    apply hoare_bind _ _ (anyWG _)
    intro d
    apply hoare_bind _ _ (anyWG _)
    intro ipv4
    split
    · simpa only [pure_bind] using digest d.cookieSecret (netBytes src.saddr 4)
    · apply hoare_bind _ _ (anyWG _)
      intro ipv6
      split
      · simpa only [pure_bind] using digest d.cookieSecret (netBytes src.saddr 16)
      · simpa only [pure_bind] using digest d.cookieSecret []
  unfold makeCookie
  apply hoare_bind _ _ (anyWG _)
  intro d
  apply hoare_bind _ _ (anyWG _)
  intro expired
  split
  · apply hoare_bind _ _ (anyWG _)
    intro birthdate
    apply hoare_bind _ _ (anyWG _)
    intro secret
    apply hoare_bind _ _ (anyWG _)
    intro done
    exact tail
  · exact tail

theorem makeCookie_length (src : SkbSource) (w v : WGWorld) (a b : Ambient)
    (bytes : List UInt8)
    (run : ((makeCookie src).run w).run a = .ok ((bytes,v),b)) : bytes.length = 16 :=
  (hoare_iff_run_ambient _ _ _).mp (makeCookie_size_spec src) w a bytes v b trivial run

end Leanux.Proofs.WG.AuthenticatedEffects
