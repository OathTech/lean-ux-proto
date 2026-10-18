import Leanux.Proofs.WG.TransmitSecurity.NonceFrames
import Leanux.Proofs.WG.Origins.SessionMaterial

/-! Fresh sending counters at the original allocation point. Allocation identity
uses WGWorld.keypairCounter, so device-local slot reuse does not reuse history. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Nonce
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

theorem allocation_view (w : WGWorld) (d : Device) (peer : Option PeerId)
    (hd : w.dev = some d) :
    view (keyAllocationWorld w d peer) = (view w).fresh d.nextKeypairId := by
  apply View.ext
  · rfl
  · funext id
    simp [view, keyAllocationWorld, keyAllocationDevice, View.fresh, hd,
      Std.TreeMap.getElem?_insert]
    split <;> simp_all [eq_comm, Leanux.Proofs.WG.TransmitSecurity.Nonce.cell]

theorem create_preserves (peer : Option PeerId) (history : List Allocation) :
    Preserves (fun w => Inv (view w) history) (keypairCreate peer) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi hr
  cases result with
  | none => simpa only [Origins.create_none peer w v a b hr] using hi
  | some slot =>
    obtain ⟨d, hd, rfl, rfl⟩ := Origins.create_some peer w v slot a b hr
    rw [allocation_view w d peer hd]
    exact hi.fresh d.nextKeypairId

end Leanux.Proofs.WG.TransmitSecurity.Nonce
