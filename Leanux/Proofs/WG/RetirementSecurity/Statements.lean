import Leanux.Proofs.WG.RetirementSecurity.Consequences
import Leanux.Proofs.WG.RetirementSecurity.Clear
import Leanux.Proofs.WG.RetirementSecurity.Payments
import Leanux.Proofs.WG.RetirementSecurity.PacketPayments
import Leanux.Proofs.WG.RetirementSecurity.Holders

/-! Campaign 3, T6: local original-operation retirement contracts. The
initialized key-reference ledger, complete caller coverage and conditional
timer/worker progress remain separate obligations. No complete T6 outcome is
claimed by these exports. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing

/-- A successful original keypair put pays exactly one reference, so local
retirement cannot silently consume additional packet-held references. Zero
counts and NULL-owner failures are excluded by the actual normal-run premise,
not by a claimed initialized ownership invariant. -/
theorem original_reference_payment (id : KeypairId) (now : Bool) (w v : WGWorld)
    (a b : Ambient) (d : Device) (k : Keypair)
    (device : w.dev = some d) (resident : d.keypairs[id]? = some k)
    (run : ((keypairPut (some id) now).run w).run a = .ok (((),v),b)) :
    references v id + 1 = k.refcount :=
  (put_effect id now w v a b d k device resident run).payment

/-- A nonfinal original put retains the same allocation, sending material
and sending nonce counter; paying a reference does not reset cryptographic
state. This local claim assumes the actual normal call and its entry count. -/
theorem original_nonfinal_put (id : KeypairId) (now : Bool) (w v : WGWorld)
    (a b : Ambient) (d : Device) (k : Keypair)
    (device : w.dev = some d) (resident : d.keypairs[id]? = some k)
    (more : 1 < k.refcount)
    (run : ((keypairPut (some id) now).run w).run a = .ok (((),v),b)) :
    keyAt v id = some {k with refcount := k.refcount - 1} :=
  (put_effect id now w v a b d k device resident run).nonfinal more

/-- The final successful original put removes both the allocation and its
index entries, so lookup cannot recover retired material from this store.
This is the final-payment boundary, not a proof that all holders have paid. -/
theorem original_final_put (id : KeypairId) (now : Bool) (w v : WGWorld)
    (a b : Ambient) (d : Device) (k : Keypair)
    (device : w.dev = some d) (resident : d.keypairs[id]? = some k)
    (last : k.refcount = 1)
    (run : ((keypairPut (some id) now).run w).run a = .ok (((),v),b)) :
    keyAt v id = none ∧ Unpublished id v := by
  have effect := put_effect id now w v a b d k device resident run
  exact ⟨effect.final last,effect.unpublished (Or.inr last)⟩

/-- Immediate unreference removes index publication even when packet-held
references retain the key allocation; later lookup and retained use are
different security boundaries. The normal native call is explicit. -/
theorem original_unpublication (id : KeypairId) (w v : WGWorld)
    (a b : Ambient) (d : Device) (k : Keypair)
    (device : w.dev = some d) (resident : d.keypairs[id]? = some k)
    (run : ((keypairPut (some id) true).run w).run a = .ok (((),v),b)) :
    Unpublished id v :=
  (put_effect id true w v a b d k device resident run).unpublished (Or.inl rfl)

/-- No successful original put invents a key allocation or resets a surviving
sending nonce counter. This frame covers nullable calls and needs no key-credit
premise; it does not assert that any particular allocation must survive. -/
theorem original_put_nonce_retention (kp : Option KeypairId) (now : Bool)
    (w v : WGWorld) (a b : Ambient)
    (run : ((keypairPut kp now).run w).run a = .ok (((),v),b)) :
    v.keypairCounter = w.keypairCounter ∧
      ∀ id k, keyAt v id = some k → ∃ old, keyAt w id = some old ∧
        k.internalId = old.internalId ∧ k.sendingCounter = old.sendingCounter :=
  put_nonce_projection kp now w v a b run

/-- A normally completed original clear empties all three peer slots while
preserving every surviving key's material and nonce counter. Queued work may
retain allocations; this local theorem does not promise final-store emptiness
or timer/worker progress. -/
theorem original_clear_retirement (pid : PeerId) (w v : WGWorld) (a b : Ambient)
    (run : ((keypairsClear pid).run w).run a = .ok (((),v),b)) :
    SlotsCleared pid v ∧ Retains w v :=
  ⟨(hoare_iff_run_ambient _ _ _).mp (clear_slots pid) w a () v b True.intro run,
    clear_retains pid w v a b run⟩

/-- Reference acquisition cannot reset a surviving sending nonce counter or
invent a key allocation. This local frame includes nullable input and normal
refusal, without assuming a key-reference ledger. -/
theorem original_get_nonce_retention (kp : Option KeypairId) (w v : WGWorld)
    (a b : Ambient) (result : Option KeypairId)
    (run : ((keypairGet kp).run w).run a = .ok ((result,v),b)) :
    v.keypairCounter = w.keypairCounter ∧
      ∀ id k, keyAt v id = some k → ∃ old, keyAt w id = some old ∧
        k.internalId = old.internalId ∧ k.sendingCounter = old.sendingCounter :=
  get_nonce_projection kp w v a b result run

/-- Successful original acquisition adds exactly one reference occurrence for
the same allocation, preventing retention from being justified by unaccounted
count slack. The supplied exact ledger is local; source-holder alignment and
initialized preservation are separate obligations. -/
theorem original_key_credit_acquisition (account : Credits.Exact credits w)
    (id : KeypairId) (k : Keypair) (found : keyAt w id = some k) (a b : Ambient)
    (run : ((keypairGet (some id)).run w).run a = .ok ((some id,v),b)) :
    Credits.Exact (⟨id,k.internalId⟩ :: credits) v :=
  account.get id k found a b run

/-- Original creation starts exactly one key-reference occurrence at the new
allocation stamp. Existing allocation safety supplies slot vacancy, preventing
an overwrite from silently discarding another allocation's outstanding credits.
This is a local creation contract, not initialized ledger closure. -/
theorem original_key_credit_creation (account : Credits.Exact credits w)
    (allocation : Lifetimes.AllocationInv history w) (word : Option PeerId)
    (id : KeypairId) (a b : Ambient)
    (run : ((keypairCreate word).run w).run a = .ok ((some id,v),b)) :
    Credits.Exact (⟨id,w.keypairCounter + 1⟩ :: credits) v :=
  account.create allocation word id a b run

/-- A successful original put pays its selected key-reference occurrence and
leaves all remaining occurrences exactly funded. The explicit incoming ledger
does not itself identify slots, packet holders or saved worker references. -/
theorem original_key_credit_payment (account : Credits.Exact (allocation :: credits) w)
    (now : Bool) (a b : Ambient)
    (run : ((keypairPut (some allocation.slot) now).run w).run a = .ok (((),v),b)) :
    Credits.Exact credits v :=
  account.put now a b run

/-- Paying the last occurrence in a supplied exact key ledger removes the
allocation and index publication. This derives the native last-reference test
from accounting; initialized source-holder completeness remains unproved. -/
theorem original_last_credit_retirement (account : Credits.Exact (allocation :: credits) w)
    (last : allocation ∉ credits) (now : Bool) (a b : Ambient)
    (run : ((keypairPut (some allocation.slot) now).run w).run a = .ok (((),v),b)) :
    keyAt v allocation.slot = none ∧ Unpublished allocation.slot v :=
  account.put_last last now a b run

/-- An outstanding occurrence in a supplied exact key ledger prevents a
successful original put from deleting its allocation or changing its material
and nonce counter. Transport from actual source holders is still required. -/
theorem original_outstanding_credit_retention (account : Credits.Exact (allocation :: credits) w)
    (outstanding : allocation ∈ credits) (now : Bool) (a b : Ambient)
    (run : ((keypairPut (some allocation.slot) now).run w).run a = .ok (((),v),b)) :
    ∃ k, keyAt w allocation.slot = some k ∧ k.internalId = allocation.stamp ∧
      keyAt v allocation.slot = some {k with refcount := k.refcount - 1} :=
  account.put_outstanding outstanding now a b run

/-- The original clear pays the references in the peer's actual three
publication slots, preserving exact funding and cryptographic state for every
remaining occurrence. This source-local result permits aliased slots and
assumes their explicit stamped account; initialized holder transport remains
an obligation. -/
theorem original_clear_slot_credits (pid : PeerId) (p : Peer) (loans : SlotLoans)
    (remaining : Credits.Ledger) (aligned : loans.Aligned p)
    (account : PeerAccount pid p (loans.credits ++ remaining) w) (a b : Ambient)
    (run : ((keypairsClear pid).run w).run a = .ok (((),v),b)) :
    Credits.Exact remaining v ∧ SlotsCleared pid v ∧
      ∀ allocation ∈ remaining, ∃ before after,
        keyAt w allocation.slot = some before ∧ keyAt v allocation.slot = some after ∧
        after.internalId = allocation.stamp ∧ keyCore after = keyCore before := by
  have funded := (hoare_iff_run_ambient _ _ _).mp
    (clear_slot_account pid p loans remaining aligned) w a () v b account run
  have retained := clear_retains pid w v a b run
  refine ⟨funded.2,(original_clear_retirement pid w v a b run).1,?_⟩
  intro allocation held
  obtain ⟨after,found,stamp,_⟩ := funded.2.resident held
  obtain ⟨before,old,same⟩ := retained.keys allocation.slot after found
  exact ⟨before,after,old,found,stamp,same⟩

/-- Native TX disposal pays one key reference for the batch, even when it
contains multiple skbs, preventing packet count from consuming other holders'
references. The paid allocation is the supplied saved head loan; its transfer
from the original TX selection is still a caller obligation. -/
theorem original_tx_batch_credit_disposal (pid : PeerId) (items : List SkbId)
    (allocation : Credits.Allocation) (remaining : Credits.Ledger)
    (account : Credits.Exact (allocation :: remaining) w) (a b : Ambient)
    (run : ((Queues.TxDisposition.disposeSource pid items allocation.slot).run w).run a =
      .ok ((result,v),b)) : Credits.Exact remaining v :=
  (hoare_iff_run_ambient _ _ _).mp (Credits.tx_dispose_account pid items allocation remaining)
    w a result v b account run

/-- The literal RX cleanup pays exactly the saved packet's key occurrence;
the separate peer payment and packet free cannot spend another key reference.
The selected packet's stamped loan and the exact incoming account are explicit
local premises, not an initialized ownership claim. -/
theorem original_rx_credit_cleanup (id : SkbId) (pkt : RxPacket) (flag : Bool)
    (allocation : Credits.Allocation) (remaining : Credits.Ledger)
    (key : pkt.keypair = allocation.slot) (account : Credits.Exact (allocation :: remaining) w)
    (a b : Ambient)
    (run : ((Queues.RxCredits.cleanup id pkt flag).run w).run a = .ok (((),v),b)) :
    Credits.Exact remaining v :=
  (hoare_iff_run_ambient _ _ _).mp (Credits.rx_cleanup_account id pkt flag allocation remaining key)
    w a () v b account run

/-- The initialized fixture has no unaccounted key holders: its actual slots,
RX queues and TX batches project to an empty funded ledger. This establishes
only the initialized base case; whole-run preservation is not claimed. -/
theorem initialized_key_holders (net bare : Bool) :
    HolderAccount [] (Runner.initialWG net bare) := initial_holder_account net bare

end Leanux.Proofs.WG.RetirementSecurity
