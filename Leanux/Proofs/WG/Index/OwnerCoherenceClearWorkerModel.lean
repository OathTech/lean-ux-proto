import Leanux.Proofs.WG.Index.OwnerCoherenceSlotRemovalModel
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

/-- The identity word read by the actual clear-worker peek, after passive records. -/
def clearWorkerUnit (records : Option (List HiddenRecord)) : Option Nat :=
  match records.map (fun rs => rs.dropWhile fun r => HiddenSite.passive r.site) with
  | some (r :: _) =>
    if r.site != (HiddenSite.sectionStart .clearPeerWorker).info.id || r.bytes.length < 16 then none
    else let u := recordWordOf r.bytes 1
         if u == 0 then none else some u
  | _ => none

/-- Exactly the named queued peer, or the queue head when no identity is supplied.
A missing device/head, unknown named unit or unqueued named peer has no selection. -/
def clearWorkerSelected (s : Campaign2.Product.Snapshot) : Option PeerId := do
  let d ← s.wg.device
  let head ← d.clearWorkQueue.head?
  match clearWorkerUnit s.ambient.hidden with
  | none => return head
  | some unit =>
    let (_,_,pid) ← s.ambient.unitPeers.find? fun e => e.1 == unit && e.2.1 == Worker.clearPeerWorker.index
    if d.clearWorkQueue.contains pid then some pid else none

/-- Only the actual selected queued peer owes last-reference slot coverage. -/
def ClearWorkerOwnerEntry (s : Campaign2.Product.Snapshot) : Prop :=
  View.OwnerCoherentSafe s.toSnapshot ∧
  ∀ pid, clearWorkerSelected s = some pid → ∃ d p,
    s.wg.device = some d ∧ d.peers[pid]? = some p ∧ 0 < p.refcount ∧ LastOwnerCovered d pid p

end Leanux.Proofs.WG.Index
