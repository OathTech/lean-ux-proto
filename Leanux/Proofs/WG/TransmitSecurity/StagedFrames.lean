import Leanux.Proofs.WG.HandshakeSecurity.FreshnessFrames

/-! Exact staged plaintext and peer-allocation projection. Ordinary peer updates
preserve this view; queue edits and final peer release have separate contracts. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged
open Leanux Leanux.WG Leanux.Proofs.Framing

def stagedAt (w : WGWorld) (pid : PeerId) : Option (Nat × List Packet) :=
  (w.dev.bind fun d => d.peers[pid]?).map fun p => (p.internalId, p.staged)

def Retains (w v : WGWorld) : Prop :=
  ∀ pid value, stagedAt v pid = some value → stagedAt w pid = some value

theorem Retains.refl (w : WGWorld) : Retains w w := fun _ _ h => h

theorem Retains.trans {u v w : WGWorld} (uv : Retains u v) (vw : Retains v w) :
    Retains u w := fun pid value found => uv pid value (vw pid value found)

theorem modifyPeer_staged (pid : PeerId) (f : Peer → Peer)
    (same : ∀ p, (f p).internalId = p.internalId ∧ (f p).staged = p.staged)
    (w v : WGWorld) (a b : Ambient) (x : Unit)
    (run : (((do setPeer pid (f (← getPeer pid))) : WG.M Unit).run w).run a =
      .ok ((x, v), b)) : Retains w v := by
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p, read, ambient, getter, setter⟩ := run
  obtain ⟨hw, ha, d, hd, hp⟩ := Queues.getPeer_normal pid w read p a ambient getter
  subst read
  subst ambient
  change Except.ok (((), {w with dev := w.dev.map fun d =>
    {d with peers := d.peers.insert pid (f p)}}), a) = .ok ((x, v), b) at setter
  simp only [hd, Option.map_some, Except.ok.injEq, Prod.mk.injEq] at setter
  rw [← setter.1.2]
  intro j stamp found
  simp only [stagedAt, hd, Option.bind_some, Std.TreeMap.getElem?_insert,
    Std.LawfulEqOrd.compare_eq_iff_eq] at found ⊢
  by_cases sameSlot : pid = j
  · subst j
    simpa [hp, same p] using found
  · simpa [sameSlot] using found

theorem getDev_staged (w v : WGWorld) (a b : Ambient) (d : Device)
    (run : (getDev.run w).run a = .ok ((d, v), b)) : Retains w v := by
  cases hd : w.dev with
  | none => simp [getDev, hd, invariant, AmbientM.invariant] at run; cases run
  | some current =>
    simp [getDev, hd] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact .refl _


end Leanux.Proofs.WG.TransmitSecurity.Staged
