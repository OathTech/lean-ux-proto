import Leanux.Proofs.WG.Config.RequestRefusalModel
import Leanux.Proofs.WG.Config.RequestOrderEffects

/-! The key and peer continuation languages cannot add a device-port receipt. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.RequestOrder
open Leanux Leanux.WG

theorem NoRefusal.append {left right : List Receipt}
    (hl : NoRefusal left) (hr : NoRefusal right) : NoRefusal (left ++ right) := by
  intro r member
  rcases List.mem_append.mp member with old | new
  · exact hl r old
  · exact hr r new

theorem NoRefusal.final {h : List Receipt} (point : NoRefusal h)
    (ret : Int) (final : Campaign2.State) : RefusalFinal ret h final :=
  fun r member refused => False.elim (point r member refused)

theorem event_refusalSilent (kind : Kind) (silent : ∀ port, kind ≠ .port port) :
    RefusalSilent (Language.event kind) := by
  intro h point
  rcases point with rfl | ⟨r,rfl,selected⟩
  · simp [NoRefusal]
  · intro other member ⟨⟨port,k⟩,_⟩
    have equal : other = r := by simpa using member
    subst other
    exact silent port (selected.symm.trans k)

theorem bind_refusalSilent {α β : Type} {A : Language α} {B : α → Language β}
    (silent : RefusalSilent A) (prefixes : ∀ ret h, A.normal ret h → A.prefixes h)
    (next : ∀ ret, RefusalSilent (B ret)) : RefusalSilent (A.bind B) := by
  intro h point
  rcases point with first | ⟨ret,left,right,first,last,rfl⟩
  · exact silent h first
  · exact (silent left (prefixes ret left first)).append (next ret right last)

theorem peers_refusalSilent (attrs : DeviceAttrs) : RefusalSilent (Language.peers attrs) := by
  intro h point r member ⟨⟨port,kind⟩,_⟩
  have eq : peerReceipts h = h := PeerPartial.peerReceipts point
  have selected : r ∈ peerReceipts h := by rw [eq]; exact member
  simp only [peerReceipts,List.mem_filter] at selected
  cases k : r.kind <;> simp_all

theorem keyed_refusalSilent (attrs : DeviceAttrs) : RefusalSilent (keyedLanguage attrs) := by
  exact bind_refusalSilent (event_refusalSilent .keyStage (by intro p h; cases h))
    (by intro ret h point; obtain ⟨r,eq,k,_⟩ := point; exact Or.inr ⟨r,eq,k⟩) (fun _ => peers_refusalSilent attrs)

theorem afterPort_refusalSilent (attrs : DeviceAttrs) (flags : UInt32) :
    RefusalSilent (afterPortLanguage attrs flags) := by
  unfold afterPortLanguage
  split
  · exact bind_refusalSilent (event_refusalSilent .replacement (by intro p h; cases h))
      (by intro ret h point; obtain ⟨r,eq,k,_⟩ := point; exact Or.inr ⟨r,eq,k⟩) (fun _ => keyed_refusalSilent attrs)
  · exact keyed_refusalSilent attrs

end Leanux.Proofs.WG.Config.RequestOrder
