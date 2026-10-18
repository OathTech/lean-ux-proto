import Leanux.Proofs.WG.Index.RetirementModel
import Leanux.Proofs.WG.Index.HashSlotReleaseClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceReleaseClaims
import Leanux.Proofs.WG.Index.FundedBaseSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise
open Queues.RxCredits Queues.RxCredits.DurableHolders

/-- An explicit additional retirement occurrence funds a second reference;
this uses multiplicity and does not manufacture a reservation from slack. -/
theorem retired_loan_credit
    {holders : DurableHolders} {cs : Ledger} {retired : Reservations}
    {w : WGWorld} {d : Device} {pid : PeerId} {p : Peer}
    (funded : holders.Funded cs (⟨d.ifindex,pid,p.internalId⟩ :: retired) w)
    (device : w.dev = some d) (resident : d.peers[pid]? = some p)
    (reserved : (⟨d.ifindex,pid,p.internalId⟩ : Owner) ∈ retired) :
    2 ≤ p.refcount := by
  have positive : 0 < retired.count ⟨d.ifindex,pid,p.internalId⟩ :=
    List.count_pos_iff.mpr reserved
  have bound : demand cs (holders.owners ++ (⟨d.ifindex,pid,p.internalId⟩ :: retired))
      ⟨d.ifindex,pid,p.internalId⟩ ≤ p.refcount := by
    simpa only [balance,resident_at device resident,Option.map_some,Option.getD_some]
      using funded.carriers.funded ⟨d.ifindex,pid,p.internalId⟩
  simp only [demand,List.count_append,List.count_cons_self] at bound
  omega

/-- The actual paid loan alone supplies positivity for the resident allocation. -/
theorem paid_loan_positive
    {holders : DurableHolders} {cs : Ledger} {retired : Reservations}
    {w : WGWorld} {d : Device} {pid : PeerId} {p : Peer}
    (funded : holders.Funded cs (⟨d.ifindex,pid,p.internalId⟩ :: retired) w)
    (device : w.dev = some d) (resident : d.peers[pid]? = some p) :
    0 < p.refcount := by
  have bound : demand cs (holders.owners ++ (⟨d.ifindex,pid,p.internalId⟩ :: retired))
      ⟨d.ifindex,pid,p.internalId⟩ ≤ p.refcount := by
    simpa only [balance,resident_at device resident,Option.map_some,Option.getD_some]
      using funded.carriers.funded ⟨d.ifindex,pid,p.internalId⟩
  simp only [demand,List.count_append,List.count_cons_self] at bound
  omega

/-- A separately funded paid loan cannot be final while a coherent hashed
keypair still names its owner. Live peers retain their base occurrence; dead
hashed owners retain an explicit retirement occurrence. -/
theorem funded_lastOwnerDetached
    {holders : DurableHolders} {cs : Ledger} {retired : Reservations}
    {w : WGWorld} {d : Device} {pid : PeerId} {p : Peer}
    (configured : ConfiguredIdentity.Inv w) (base : BaseCoherence.Inv w)
    (funded : holders.Funded cs (⟨d.ifindex,pid,p.internalId⟩ :: retired) w)
    (device : w.dev = some d) (resident : d.peers[pid]? = some p)
    (coherent : HashedOwnersCoherent d) (reserved : DeadHashedReserved retired d) :
    LastOwnerDetached d pid p := by
  intro last entry member other word
  cases dead : p.isDead with
  | false =>
    have credit := FundedBase.live_loan_credit configured base funded device resident dead
    omega
  | true =>
    obtain ⟨actual,peer,actualWord,stored,_,identity⟩ := coherent entry member
    have same : actual = pid := by
      rw [word] at actualWord
      exact Option.some.inj (Option.some.inj actualWord).symm
    subst actual
    have samePeer : peer = p := Option.some.inj (stored.symm.trans resident)
    subst peer
    cases owner : entry.owner with
    | handshake target =>
      have targetSame : pid = target := by simpa only [owner] using identity
      exact other (owner.trans (congrArg IndexOwner.handshake targetSame.symm))
    | keypair kid =>
      obtain ⟨key,keyFound,_⟩ := (show ∃ key, d.keypairs[kid]? = some key ∧
        0 < key.refcount by simpa only [owner] using identity)
      have keyPeer : key.peer = some pid := by
        simpa only [owner,ownerWord,keyFound,Option.map_some,Option.some.injEq] using word
      have retiredMember := reserved entry member kid key pid p owner keyFound keyPeer resident dead
      have credit := retired_loan_credit funded device resident retiredMember
      omega

/-- Last-release detachment is enough for slot coverage. Unhashed residual
slots need not be empty: they create no surviving table obligation. -/
theorem releasedPeer_hashSlotCoverage_detached (d : Device) (pid : PeerId) (p : Peer)
    (resident : d.peers[pid]? = some p) (detached : LastOwnerDetached d pid p)
    (covered : HashSlotCoverage d) :
    HashSlotCoverage (releasedPeerDevice d pid p) := by
  by_cases last : p.refcount = 1
  · intro entry member kid owner
    have old : entry ∈ d.indexTable := by
      rw [releasedPeer_table,last,ite_eq_left rfl] at member
      exact (List.mem_filter.mp member).1
    obtain ⟨target,peer,key,found,keyFound,keyPeer,slot⟩ := covered entry old kid owner
    have different : pid ≠ target := by
      intro same
      subst target
      have word : ownerWord d entry.owner = some (some pid) := by
        simp only [owner,ownerWord,keyFound,Option.map_some,keyPeer]
      exact detached last entry old (by rw [owner]; intro impossible; cases impossible) word
    refine ⟨target,peer,key,?_,?_,keyPeer,slot⟩
    · rw [releasedPeer_other pid target d p different]
      exact found
    · rw [releasedPeer_keypairs]
      exact keyFound
  · exact nonlastPeerRelease_hashSlotCoverage d pid p resident last covered

end Leanux.Proofs.WG.Index
