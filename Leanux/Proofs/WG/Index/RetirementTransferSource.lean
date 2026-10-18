import Leanux.Proofs.WG.Index.RetirementTransferEffects
import Leanux.Proofs.WG.Index.RetirementModel
import Leanux.Proofs.WG.Index.FundedBaseSource
import Leanux.Proofs.WG.Index.AipRemovalFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.Framing
open Queues.RxCredits Queues.RxCredits.DurableHolders Lifetimes

/-- Original make-dead transfers newly retired hashed owners to precisely the
detached stamped base occurrences. No new source traversal is introduced. -/
theorem peerMakeDead_deadHashedReserved
    (pid : PeerId) (holders : DurableHolders) (cs : Ledger)
    (loans retired : Reservations) (w v : WGWorld) (a b : Ambient)
    (configured : ConfiguredIdentity.Inv w) (base : BaseCoherence.Inv w)
    (funded : holders.Funded cs loans w)
    (reserved : ∀ d, w.dev = some d → DeadHashedReserved retired d)
    (run : ((peerMakeDead pid).run w).run a = .ok (((),v),b)) :
    ∀ final, v.dev = some final →
      DeadHashedReserved (BaseRemoval.detached holders.base pid ++ retired) final := by
  have identity :=
    (pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherence.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.makeDead_configured)
      pid w v a b run
  have table := peerMakeDead_spec_tableCursor_variant pid _ w a () v b rfl run
  have keys := congrArg (fun x => x.1.2.2.2.1)
    (BaseRemoval.peerMakeDead_normal pid w v a b run).1
  intro final out
  cases device : w.dev with
  | none =>
    simp [ConfiguredIdentity.view,device,out] at identity
  | some d =>
    have cells : ConfiguredIdentity.state final =
        (ConfiguredIdentity.state d).kill pid := by
      simpa only [ConfiguredIdentity.view,device,out,Option.map_some,Option.some.injEq]
        using identity
    have sameTable : final.indexTable = d.indexTable := by
      have pair : TimerDiscipline.tableCursor final = TimerDiscipline.tableCursor d := by
        simpa only [out,device,Option.map_some,Option.some.injEq] using table
      exact congrArg Prod.fst pair
    have sameWords : ∀ (kid : KeypairId), (final.keypairs[kid]?).map Keypair.peer =
        (d.keypairs[kid]?).map Keypair.peer := by
      intro kid
      simpa only [DecryptCarrier.decryptView,carrierView,keyView,keyWords,
        out,device,Option.bind_some] using congrFun keys kid
    apply deadHashedReserved_mark retired (BaseRemoval.detached holders.base pid)
      d final pid (reserved d device) sameTable sameWords cells
    intro p resident live
    exact BaseRemoval.detached_member
      (FundedBase.live_base_reservation configured base funded device resident live) rfl

/-- The reservation transport and the landed accounting transfer refer to
the same actual make-dead execution, preserving every list occurrence. -/
theorem peerMakeDead_retirement_step
    (pid : PeerId) (holders : DurableHolders) (cs : Ledger)
    (retired loans : Reservations) (w v : WGWorld) (a b : Ambient)
    (configured : ConfiguredIdentity.Inv w) (base : BaseCoherence.Inv w)
    (funded : holders.Funded cs (retired ++ loans) w) (stable : StableRx cs w)
    (reserved : ∀ d, w.dev = some d → DeadHashedReserved retired d)
    (run : ((peerMakeDead pid).run w).run a = .ok (((),v),b)) :
    (holders.withoutBase (BaseRemoval.live holders.base pid)).Funded cs
      ((BaseRemoval.detached holders.base pid ++ retired) ++ loans) v ∧
    StableRx cs v ∧ ConfiguredIdentity.Inv v ∧ BaseCoherence.Inv v ∧
    (∀ final, v.dev = some final →
      DeadHashedReserved (BaseRemoval.detached holders.base pid ++ retired) final) := by
  obtain ⟨after,stillStable⟩ :=
    DurableHolders.peerMakeDead_funded pid funded stable a b run
  refine ⟨?_,stillStable,
    ConfiguredIdentity.peerMakeDead_preserves pid w v a b configured run,
    BaseCoherence.makeDead_preserves pid base a b run,
    peerMakeDead_deadHashedReserved pid holders cs (retired ++ loans)
      retired w v a b configured base funded reserved run⟩
  simpa only [List.append_assoc] using after

end Leanux.Proofs.WG.Index
