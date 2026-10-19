import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeFreshDriver
import Leanux.Proofs.WG.AuthenticatedEffects.CausalJournalOldProjection
import Leanux.Proofs.WG.TransmitSecurity.JournalHandshakeProjection

/-! The newest native handshake admission is carried through the actual outer
runner and both exact journal projections. The callbacks and admissions are
positions in one execution, including prefixes retained before Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.HandshakeFresh
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity

theorem initialized (trace : Runner.Trace) (placeholders : Bool) :
    Safe (runPrefixOuter (Driver.executeObserved HandshakeDriver.hooks trace placeholders) []).2 :=
  Driver.initialized_actor_history DriverProof.actors empty_safe trace placeholders

theorem initialized_old (trace : Runner.Trace) (placeholders : Bool) :
    Safe ((runPrefixOuter (Journal.execute trace placeholders) []).2.filterMap Journal.handshake?) := by
  have projected := congrArg Prod.snd (Journal.HandshakeProjection.execute trace placeholders [])
  simp only [List.filterMap_nil] at projected
  rw [← projected]
  exact initialized trace placeholders

theorem initialized_final (trace : Runner.Trace) (placeholders : Bool) :
    Safe ((runPrefixOuter (CausalJournal.execute trace placeholders) []).2.filterMap CausalJournal.handshake?) := by
  have safe := initialized_old trace placeholders
  have projected := congrArg Prod.snd (CausalJournal.execute_projects trace placeholders [])
  simp only [List.filterMap_nil] at projected
  rw [projected] at safe
  change Safe ((runPrefixOuter (CausalJournal.execute trace placeholders) []).2.filterMap
    (fun event => (CausalJournal.old? event).bind Journal.handshake?))
  simpa only [List.filterMap_filterMap] using safe

/-- The exact callback's prefix contains its latest successful native consumer
admission; another admission cannot intervene between that receipt and callback. -/
theorem callback_latest (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List CausalJournal.Event) (kind : HandshakeCausal.Kind) (pid : PeerId)
    (position : (runPrefixOuter (CausalJournal.execute trace placeholders) []).2 =
      pre ++ .old (.handshake (.callback kind pid)) :: post) :
    Available (pre.filterMap CausalJournal.handshake?) pid := by
  have safe := initialized_final trace placeholders
  apply safe (pre.filterMap CausalJournal.handshake?) (.callback kind pid)
    (post.filterMap CausalJournal.handshake?)
  rw [position]
  simp only [List.filterMap_append,List.filterMap_cons,CausalJournal.handshake?,
    CausalJournal.old?,Journal.handshake?,Option.bind_some]

end Leanux.Proofs.WG.AuthenticatedEffects.HandshakeFresh
