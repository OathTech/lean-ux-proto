import Leanux.Proofs.WG.Progress.AllocationProgressSource
import Leanux.Proofs.WG.Config.AllowedTransferOperations
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.AllowedFinite
open Leanux Leanux.WG

/-- The original node allocation with bounded concrete allocation encounters. -/
def allocate (site : AllocSite) (node : AipNode) : AipM (Option NodeId) := do
  if !(← monadLift (hiddenAllocFinite site)) then return none
  let id := (← get).nextNode
  modify fun s => {s with nextNode := id + 1, nodes := s.nodes.insert id node}
  return some id

theorem allocate_source (site : AllocSite) (node : AipNode) :
    WG.allocNode site node = allocate site node := by
  unfold WG.allocNode allocate
  have allocation : (hiddenAlloc site : AipM Bool) =
      monadLift (hiddenAllocFinite site) := by
    change monadLift (AmbientM.hiddenAlloc site) = _
    rw [hiddenAlloc_finite_source]
  rw [allocation]

/-- The original add prefix and shared owned stages with finite allocation;
lookup, placement and trie updates retain their actual fixed/list bounds. -/
def add (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) : WG.M Int := do
  if ← branchCmp .addCidrTooLong (cidr > bits) cidr bits then return -EINVAL
  if ← branch .addNoPeer peer.isNone then return -EINVAL
  let some pid := peer | invariant "unreachable"
  let trie ← slotGet root
  Config.addRootSourceWith allocate root bits key cidr pid trie

theorem add_source (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) :
    WG.add root bits key cidr peer = add root bits key cidr peer := by
  rw [Config.add_transfer_source]
  unfold add Config.addRootSource
  have allocation : WG.allocNode = allocate := funext fun site => funext (allocate_source site)
  rw [allocation]
  rfl

/-- Original family selection and sequence update followed by finite add. -/
def insert (family addr cidr : Nat) (peer : PeerId) : WG.M Int := do
  modifyDev fun d => {d with peerAllowedips := {d.peerAllowedips with seq := d.peerAllowedips.seq + 1}}
  if family == 4 then add .root4 32 addr cidr (some peer)
  else add .root6 128 addr cidr (some peer)

theorem insert_source (family addr cidr : Nat) (peer : PeerId) :
    WG.insert family addr cidr peer = insert family addr cidr peer := by
  simp only [WG.insert, insert, add_source]

end Leanux.Proofs.WG.Progress.AllowedFinite
