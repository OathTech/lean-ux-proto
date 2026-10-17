import Leanux.Proofs.WG.Config.CursorCallbackModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

def cursorHeaderSkb (d : Device) (ctx : DumpCtx) (skb0 : NlSkb) : NlSkb :=
  let skb := (skb0.put (nlmsgTotal 4)).2
  if ctx.nextPeer.isNone then
    let skb := (skb.put (nlaTotal 2)).2
    let skb := (skb.put (nlaTotal 4)).2
    let skb := (skb.put (nlaTotal 4)).2
    let skb := (skb.put (nlaTotal (d.ifname.length+1))).2
    if d.staticIdentity.hasIdentity then ((skb.put (nlaTotal 32)).2.put (nlaTotal 32)).2
    else skb
  else skb


end Leanux.Proofs.WG.Config
