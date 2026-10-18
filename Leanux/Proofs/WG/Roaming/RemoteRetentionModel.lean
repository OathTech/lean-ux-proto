import Leanux.Proofs.WG.Roaming.View

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG

/-- Remote destinations deliberately omit local address caches. They also
omit IPv6 flowinfo, which the original endpoint equality does not compare.
Map keys are mirror locations; this
does not assert identity continuity through peer recreation. -/
abbrev RemoteMap := PeerId → Option (Nat × Nat × Nat × Nat)

def remoteMap (s : Campaign2.Snapshot) : RemoteMap := remoteAt s

/-- Surviving remote destinations come from the earlier map. A removed
peer or absent endpoint is allowed; a new destination needs an explicit effect. -/
def RemoteRetained (before after : RemoteMap) : Prop :=
  ∀ pid remote, after pid = some remote → before pid = some remote

def updateRemote (before : RemoteMap) (pid : PeerId)
    (remote : Nat × Nat × Nat × Nat) : RemoteMap :=
  fun other => if other = pid then some remote else before other

theorem RemoteRetained.refl (before : RemoteMap) : RemoteRetained before before :=
  fun _ _ found => found

theorem RemoteRetained.trans {before middle after : RemoteMap}
    (first : RemoteRetained before middle) (second : RemoteRetained middle after) :
    RemoteRetained before after :=
  fun pid remote found => first pid remote (second pid remote found)

theorem RemoteRetained.of_eq {before after : RemoteMap} (same : after = before) :
    RemoteRetained before after := by
  rw [same]
  exact .refl before

theorem RemoteRetained.update {before after : RemoteMap}
    (kept : RemoteRetained before after) (pid : PeerId) (remote : Nat × Nat × Nat × Nat) :
    RemoteRetained (updateRemote before pid remote) (updateRemote after pid remote) := by
  intro other value found
  by_cases same : other = pid
  · simpa only [updateRemote, same, ite_true] using found
  · simpa only [updateRemote, same, ite_false] using
      kept other value (by simpa only [updateRemote, same, ite_false] using found)

theorem RemoteRetained.updated_selected {before after : RemoteMap}
    {pid : PeerId} {remote value : Nat × Nat × Nat × Nat}
    (kept : RemoteRetained (updateRemote before pid remote) after)
    (found : after pid = some value) : value = remote := by
  have equal := kept pid value found
  simpa only [updateRemote, ite_true, Option.some.injEq] using equal.symm

theorem RemoteRetained.updated_other {before after : RemoteMap}
    {pid other : PeerId} {remote value : Nat × Nat × Nat × Nat}
    (kept : RemoteRetained (updateRemote before pid remote) after)
    (different : other ≠ pid) (found : after other = some value) :
    before other = some value := by
  simpa only [updateRemote, different, ite_false] using kept other value found

end Leanux.Proofs.WG.Roaming
