import Leanux.Proofs.WG.Config.MultiPeerCoalesceModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- The actual inner coalescer peer step, factored for a single DATA page.
The continuation branch is retained even though the first-false lemma below
shows it is not taken for later peers in that same page. -/
def coalescePeerStep (p : PeerDumpAttrs) (state : Array PeerDumpAttrs × Bool) :
    WG.M (ForInStep (Array PeerDumpAttrs × Bool)) := do
  let mut peers := state.1
  let first := state.2
  let continued := first && peers.size > 0 && peers.back!.split && peers.back!.publicKey == p.publicKey
  if continued then
    let last := peers.back!
    let extra := p.attrs.filter fun (k,_) => k != "public_key" && k != "allowed_ips"
    if !extra.isEmpty then invariant "op 9: a continued peer repeats attributes"
    let some (Json.arr more) := p.attrs.lookup "allowed_ips" |
      invariant "op 9: a continued peer without allowed IPs"
    let merged := last.attrs.map fun (k,v) =>
      if k == "allowed_ips" then
        (k,match v with | Json.arr a => Json.arr (a ++ more) | v => v)
      else (k,v)
    peers := peers.pop.push {last with attrs := merged,split := p.split}
  else
    peers := peers.push (peerDumpWithIps p)
  return .yield (peers,false)

/-- Once the first peer in a DATA page has been processed, all remaining
peers are appended in order with only missing allowed_ips normalization. -/
theorem coalescePeers_afterFirst (peers : List PeerDumpAttrs) (prior : Array PeerDumpAttrs) :
    forIn peers (prior,false) coalescePeerStep =
      (pure (prior ++ (peers.map peerDumpWithIps).toArray,false) : WG.M _) := by
  induction peers generalizing prior with
  | nil => simp
  | cons p ps ih =>
    simp only [List.forIn_cons,coalescePeerStep,Bool.false_and,Bool.false_eq_true,ite_false]
    change (forIn ps (prior.push (peerDumpWithIps p),false) coalescePeerStep) = _
    rw [ih]
    simp


end Leanux.Proofs.WG.Config
