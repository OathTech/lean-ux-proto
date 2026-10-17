import Leanux.Proofs.WG.Config.MultiPeerCoalesceSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- Exact coalescing of one DATA envelope followed by successful DONE.
This is a coalescer contract for arbitrary peer attributes, not a theorem that
a producer emits the page or that multiple pages form a valid dump. -/
theorem coalesce_single_page (d : Device) (peers : List PeerDumpAttrs) :
    coalesce [.data 2 (deviceFixedAttrs d) (some peers),.done 2 0] =
      pure (.ok (Json.mkObj (deviceFixedAttrs d ++ [("peers",Json.arr
        ((peers.map peerDumpWithIps).toArray.map fun p => Json.mkObj p.attrs))]))) := by
  have nonempty : deviceFixedAttrs d ≠ [] := by simp [deviceFixedAttrs]
  cases peers with
  | nil => simp [coalesce,nonempty]
  | cons p ps =>
    have rest := congrArg (fun action : WG.M (Array PeerDumpAttrs × Bool) =>
      (fun out => Except.ok (ε := Int) (Json.mkObj (deviceFixedAttrs d ++
        [("peers",Json.arr (out.1.map fun q => Json.mkObj q.attrs))]))) <$> action)
      (coalescePeers_afterFirst ps #[peerDumpWithIps p])
    unfold coalescePeerStep at rest
    simp [coalesce,nonempty,List.forIn_cons,List.forIn_nil,peerDumpWithIps,
      invariant] at rest ⊢
    apply Eq.trans ?_ rest
    congr 3

end Leanux.Proofs.WG.Config
