import Leanux.Proofs.WG.Index.SelectedSendRetirementSource
import Leanux.Proofs.WG.Index.RetirementBeforePaymentSource

set_option autoImplicit false

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Leanux.Proofs.Framing
open Queues.RxCredits Queues.RxCredits.DurableHolders Lifetimes Std.Do

/-- Only the funded loan order is changed. Retirement roots and every
multiplicity remain intact. -/
theorem RetirementWork.loans_perm
    {original : DurableHolders} {cs : Ledger} {loans other retired : Reservations}
    {w : WGWorld} (hi : RetirementWork original cs loans retired w)
    (order : loans.Perm other) :
    RetirementWork original cs other retired w := by
  obtain ⟨holders,remainder,funded,stable⟩ := hi.account
  refine ⟨⟨holders,remainder,?_,stable⟩,hi.configured,hi.base,hi.covered,hi.coherent,hi.reserved⟩
  exact ⟨funded.aligned,WorkReservations.carrier_loans_perm funded.carriers
    (order.append_left holders.owners)⟩

/-- Recover the actual selected work occurrence from the existing funded
account, run the original flushed send, and retain its original remainder
relation. The only supplied leaf is the original initiation-index contract. -/
theorem flushedSend_retirementWork
    (original : DurableHolders) (cs : Ledger) (retired loans : Reservations)
    (initiation : ∀ holders paid, InitiationIndexContract holders cs paid retired loans) :
    SelectedDrain.SendKeeps (RetirementWork original cs (retired ++ loans) retired)
      runFlushedSendWork := by
  intro w v d pid a b hi device member run
  obtain ⟨holders,remainder,funded,stable⟩ := hi.account
  obtain ⟨paid,rest,selected⟩ := WorkReservations.select_exists holders.send pid
    ((funded.aligned.send d device) ▸ member)
  obtain ⟨credit,stillStable,configured,base,safe⟩ := flushed_send_retirement
    holders cs pid paid rest retired loans selected
    (initiation (holders.withoutSend rest) paid)
    w v a b hi.configured hi.base funded stable
      ⟨hi.covered,hi.coherent,hi.reserved⟩ run
  refine ⟨⟨holders.withoutSend rest,?_,credit,stillStable⟩,
    configured,base,safe.1,safe.2.1,safe.2.2⟩
  exact remainder.trans
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderDrains.«0».Leanux.Proofs.WG.Queues.RxCredits.DurableHolders.WorkRemainder.send_step) selected)

/-- The caller's outstanding payment remains separately funded while a
selected send occurrence is taken and paid. Moving the caller occurrence
past the retirement list changes neither counts nor retirement duties. -/
theorem flushedSend_paidRetirementWork
    (original : DurableHolders) (cs : Ledger) (paid : Owner)
    (retired loans : Reservations)
    (initiation : ∀ holders selected,
      InitiationIndexContract holders cs selected retired (paid :: loans)) :
    SelectedDrain.SendKeeps
      (RetirementWork original cs (paid :: (retired ++ loans)) retired)
      runFlushedSendWork := by
  intro w v d pid a b hi device member run
  have order : (paid :: (retired ++ loans)).Perm (retired ++ paid :: loans) :=
    List.perm_middle.symm
  have after := flushedSend_retirementWork original cs retired (paid :: loans)
    initiation w v d pid a b (hi.loans_perm order) device member run
  exact after.loans_perm order.symm

/-- Actual after-dead removal with its selected-send obligation discharged.
Only the original initiation-index family remains conditional; the account
retains the unpaid retirement list in order, with multiplicity. -/
theorem peerRemoveAfterDead_retirement_initiation
    (original : DurableHolders) (cs : Ledger) (paid : Owner)
    (retired loans : Reservations)
    (initiation : ∀ holders selected,
      InitiationIndexContract holders cs selected retired (paid :: loans)) :
    Ensures (peerRemoveAfterDead paid.slot)
      (RetirementWork original cs (paid :: (retired ++ loans)) (paid :: retired))
      (fun _ => RetirementWork original cs (retired ++ loans) retired) :=
  peerRemoveAfterDead_retirement original cs paid retired loans
    (flushedSend_paidRetirementWork original cs paid retired loans initiation)

end Leanux.Proofs.WG.Index
