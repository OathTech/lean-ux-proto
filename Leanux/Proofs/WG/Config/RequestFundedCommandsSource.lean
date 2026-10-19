import Leanux.Proofs.WG.Config.RequestFundedCommandsFrames
import Leanux.Proofs.WG.Config.RequestFundedCommandsBridge
import Leanux.Proofs.WG.Config.RequestWgChainClaims
import Leanux.Proofs.WG.Config.KeyStageEntryClaims
import Leanux.Proofs.WG.Config.ConfiguredCommandClaims

/-! Account propagation through the already-proved receipt chain. Every native command contract is applied to the same valid receipt; no operational loop or observer is added. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.RequestOrder.FundedCommands
open Leanux Leanux.WG Queues Queues.RxCredits AllowedIps Configuration
open Leanux.Proofs.WG.Config.OwnerConfiguration

theorem chain_entries (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs)
    {start finish : Campaign2.State} {rs : List Receipt}
    (chain : WgLinks.Chain start rs finish)
    (valid : ∀r∈rs,Valid attrs r)
    (commands : ∀r∈rs,∃p,r.kind=.peer p ∧ PeerAddressShape p)
    (prior : Campaign2.Snapshot) (pre : ProjectedEntry cs loans prior)
    (same : prior.wg=start) :
    ∀r∈rs,ProjectedEntry cs loans r.before ∧ ProjectedEntry cs loans r.after := by
  induction chain generalizing prior with
  | nil state=>intro r member;cases member
  | @cons state final head rest before tail ih=>
    have input:=entry_at_receipt cs loans attrs prior head
      (valid head (by simp)) pre (before.trans same.symm)
    obtain ⟨p,kind,shape⟩:=commands head (by simp)
    have output:=Valid.ensures (valid head (by simp)) kind
      (original_command cs loans p shape) input
    intro r member
    rcases List.mem_cons.mp member with equal|later
    · subst r
      exact ⟨input,output⟩
    · exact ih (fun r member=>valid r (List.mem_cons_of_mem head member))
        (fun r member=>commands r (List.mem_cons_of_mem head member))
        head.after output rfl r later

end Leanux.Proofs.WG.Config.RequestOrder.FundedCommands

namespace Leanux.Proofs.WG.Config.RequestOrder.FundedCommands
open Leanux Leanux.WG Queues Queues.RxCredits AllowedIps Configuration
open Leanux.Proofs.WG.Config.OwnerConfiguration

theorem certificate_entries (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs)
    (shape : DeviceAddressShape attrs) (initial : Campaign2.Snapshot) (result : Inspection)
    (certificate : Certificate attrs initial result) (pre : ProjectedEntry cs loans initial) :
    Entries cs loans result.receipts := by
  rcases request_keyOrEmpty attrs result.receipts certificate.1.2.2.1 with empty|⟨key,member,kind⟩
  · intro r selected
    rw [empty] at selected
    cases selected
  · have keyEffect:=KeyStage.certificate_initial_effects cs loans attrs initial result certificate pre
      key member kind
    obtain ⟨endpoint,chain⟩:=WgLinks.certificate_peer_chain attrs initial result certificate key member kind
    exact chain_entries cs loans attrs chain
      (fun r hr=>certificate.1.2.1 r (List.mem_filter.mp hr).1)
      (request_peer_shape attrs shape result.receipts certificate.1.2.2.1)
      key.after keyEffect.2.2.1 rfl

theorem account_matches (cs : Ledger) (loans : Reservations)
    (r : Receipt) (p : PeerAttrs) (nested : AllowedOrder.Inspection)
    (matched : PeerCommandMatches r p nested)
    (before : ProjectedEntry cs loans r.before) (after : ProjectedEntry cs loans r.after) :
    AccountMatches cs loans r p nested := by
  obtain ⟨native,run,same,inspection⟩:=matched
  refine ⟨native,run,same,inspection,?_,?_⟩
  · exact (entry_snapshot cs loans native.before native.ambientBefore).mp
      (by simpa only [←same,receipt] using before)
  · exact (entry_snapshot cs loans native.after native.ambientAfter).mp
      (by simpa only [←same,receipt] using after)

end Leanux.Proofs.WG.Config.RequestOrder.FundedCommands
