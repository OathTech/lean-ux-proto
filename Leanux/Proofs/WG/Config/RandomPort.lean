import Leanux.Proofs.WG.Config.SocketPorts

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem littleEndian_bound (bs : List UInt8) :
    bs.foldr (fun b acc => acc * 256 + b.toNat) 0 < 256 ^ bs.length := by
  induction bs with
  | nil => simp
  | cons b rest ih =>
    have hb : b.toNat < 256 := b.toNat_lt
    simp only [List.foldr_cons, List.length_cons, Nat.pow_succ]
    omega

theorem randomPortFirst_range (rand : Nat) (bounded : rand < 2 ^ 32) :
    LOCAL_PORT_LOW ≤ randomPortFirst rand ∧ randomPortFirst rand ≤ LOCAL_PORT_HIGH := by
  simp only [randomPortFirst, LOCAL_PORT_LOW, LOCAL_PORT_HIGH] at *
  omega

theorem hiddenUdp_shape (P : Kernel → Prop) :
    ⦃fun w => ⌜P w.k⌝⦄ hidden .udpPortDraw
    ⦃⇓? bs w => ⌜P w.k ∧ bs.length = 4⌝⦄ := by
  mvcgen [hidden, skipAmbient, noteNetRxStart]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [HiddenSite.info]
  all_goals omega

theorem socketInit_zero (d : Device) (net : d.creatingNet = true) :
    Ensures (socketInit 0) (fun w => w.k.wg = some d)
      (fun ret w => ret = 0 ∧ ∃ port,
        LOCAL_PORT_LOW ≤ port ∧ port ≤ LOCAL_PORT_HIGH ∧ w.k.wg = some
          { d with sock4 := some port, sock6 := some port, incomingPort := port }) := by
  have hh := hiddenUdp_shape (fun k => k.wg = some d)
  have hs := fun port => (returns_iff _ _ _).mp (socketReinit_returns (some port) (some port) d)
  rw [ensures_iff]
  simp [socketInit]
  mvcgen [getDev, getK, invariant, unsupported, hh, hs]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all
  all_goals have hb := littleEndian_bound (by assumption : List UInt8)
  all_goals simp_all
  all_goals have hr := randomPortFirst_range _ (by assumption)
  all_goals grind only

def udpDrawRecord (a b c d : UInt8) : HiddenRecord :=
  { site := HiddenSite.udpPortDraw.info.id, bytes := [a, b, c, d, 0, 0, 0, 0] }

theorem hiddenUdp_record (a b c d : UInt8) (rest : List HiddenRecord) (P : Kernel → Prop) :
    ⦃fun w => ⌜P w.k ∧ w.hidden = some (udpDrawRecord a b c d :: rest)⌝⦄ hidden .udpPortDraw
    ⦃⇓ bs w => ⌜bs = [a, b, c, d] ∧ P w.k ∧ w.hidden = some rest⌝⦄ := by
  have passive : HiddenSite.passive 125 = false := by decide
  mvcgen [hidden, skipAmbient, noteNetRxStart]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [udpDrawRecord, HiddenSite.info, passive, List.dropWhile_cons]
  all_goals obtain ⟨rfl, rfl⟩ := (show HiddenRecord.mk _ _ = _ ∧ _ from by assumption)
  all_goals simp_all

/-- The exact first candidate for a supplied four-byte UDP port draw. -/
def drawnPort (a b c d : UInt8) : Nat :=
  randomPortFirst ([a, b, c, d].foldr (fun b acc => acc * 256 + b.toNat) 0)

theorem socketInit_zero_record_returns (d : Device) (net : d.creatingNet = true)
    (a b c e : UInt8) (rest : List HiddenRecord)
    (free4 : d.sock4 ≠ some (drawnPort a b c e))
    (free6 : d.sock6 ≠ some (drawnPort a b c e)) :
    Returns (socketInit 0)
      (fun w => w.k.wg = some d ∧
        w.hidden = some (udpDrawRecord a b c e :: rest) ∧ w.portBound (drawnPort a b c e) = false)
      (fun ret w => ret = 0 ∧ w.k.wg = some
        { d with sock4 := some (drawnPort a b c e), sock6 := some (drawnPort a b c e), incomingPort := drawnPort a b c e }) := by
  have hh := hiddenUdp_record a b c e rest (fun k => k.wg = some d)
  have hs := fun port => (returns_iff _ _ _).mp (socketReinit_returns (some port) (some port) d)
  rw [returns_iff]
  simp [socketInit]
  mvcgen [getDev, getK, invariant, unsupported, hh, hs]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [drawnPort]
  all_goals grind only

end Leanux.Proofs.WG.Config
