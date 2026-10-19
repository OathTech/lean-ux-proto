import Leanux.Proofs.WG.Roaming.RemoteChronologyModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteChronology
open Leanux Leanux.WG

theorem replay_map {E F : Type} (effect : Effect E) (encode : F → E)
    (entry : RemoteMap) (events : List F) :
    replay effect entry (events.map encode) =
      replay (fun e pid => effect (encode e) pid) entry events := by
  induction events generalizing entry with
  | nil => rfl
  | cons event rest ih => exact ih _

theorem map_last {E F : Type} (effect : Effect E) (encode : F → E)
    {entry final : RemoteMap} {events : List F}
    (prior : Last (fun e pid => effect (encode e) pid) entry events final) :
    Last effect entry (events.map encode) final := by
  apply last_iff_replay.mpr
  rw [replay_map]
  exact last_to_replay prior

theorem drop_inert_prefix {E : Type} (effect : Effect E)
    {entry final : RemoteMap} {seed suffix : List E}
    (quiet : ∀ pid, Untouched effect seed pid)
    (prior : Last effect entry (seed ++ suffix) final) :
    Last effect entry suffix final := by
  apply last_iff_replay.mpr
  have retained := last_to_replay prior
  rw [replay_append] at retained
  have unchanged : replay effect entry seed = entry := by
    funext pid
    exact replay_untouched effect entry seed pid (quiet pid)
  rw [unchanged] at retained
  exact retained

end Leanux.Proofs.WG.Roaming.RemoteChronology
