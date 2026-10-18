import Leanux.Proofs.WG.Config.RoutingReadbackSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

/-- General represented insertion followed by the original fresh-peer
serializer at arbitrary room. The actual setter outcome supplies the readable
successor; no final routing or successful allocation premise is used. -/
theorem allowedip_routing_readback (d : Device) (t4 t6 : AllowedIps.Tree)
    (pid : PeerId) (p : Peer) (attrs : AllowedIpAttrs) (ctx : DumpCtx) (skb : NlSkb)
    (shape : AllowedIps.AddressShape attrs)
    (routing : AllowedIps.RoutingInvariant d t4 t6)
    (resident : d.peers[pid]? = some p)
    (fresh : ctx.nextAllowedip = none) (sequence : ctx.allowedipsSeq = 0) :
    Campaign2.Ensures (setAllowedipThenGetPeerDump pid attrs ctx skb)
      (fun s => s.wg.device = some d)
      (fun result s => ∃ out next, s.wg.device = some out ∧
        out.peers[pid]? = some next ∧
        AllowedipRoutingEffect d out t4 t6 pid attrs result.1 ∧
        (result.1 = 0 → AllowedipMoved d out t4 t6 pid attrs) ∧
        result.2 = weightedPeerResult out (routingReadNode out) next ctx skb next.allowedipsList) := by
  intro entry ambient result final after device run
  change (((setAllowedip pid attrs).run entry).run ambient >>= fun ((ret,middle),input) =>
    ((getPeerDump pid ctx skb).run middle).run input >>= fun ((dump,last),rest) =>
      Except.ok (((ret,dump),last),rest)) = _ at run
  cases setRun : ((setAllowedip pid attrs).run entry).run ambient with
  | error stop => rw [setRun] at run; cases run
  | ok output =>
    obtain ⟨⟨ret,middle⟩,input⟩ := output
    obtain ⟨out,current,effect⟩ :=
      setAllowedip_routingEffect d t4 t6 pid p attrs shape routing resident
        entry ambient ret middle input device setRun
    obtain ⟨next,u4,u6,present,invariant⟩ :=
      allowedipRoutingEffect_target d out t4 t6 pid p attrs ret routing resident effect
    obtain ⟨dump,last,rest,getRun,retained,value⟩ :=
      getPeerDump_weighted_fresh_room pid out (routingReadNode out) next ctx skb
        next.allowedipsList present fresh rfl
        (routingReadNode_readable out u4 u6 pid next invariant present) (.inl sequence)
        middle input current
    rw [setRun] at run
    change (((getPeerDump pid ctx skb).run middle).run input >>= fun ((dump,last),rest) =>
      Except.ok (((ret,dump),last),rest)) = _ at run
    rw [getRun] at run
    cases run
    refine ⟨out,next,retained,present,effect,?_,value⟩
    intro success
    exact allowedipRoutingEffect_moved d out t4 t6 pid attrs routing (success ▸ effect)

end Leanux.Proofs.WG.Config
