import Leanux.Proofs.WG.Config.HeaderLiftSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- One original normal callback: exact completed prefix and ordered cursor references.
No initial capacity, reference bound, live flag, cursor membership or sequence
consistency is assumed. Last-reference Stops remain outside normal completion. -/
theorem wgGetDeviceDump_cursor_normal (d : Device) (peers : PeerId → Peer) (ctx : DumpCtx)
    (prev : UInt32) (skb : NlSkb)
    (residents : ∀ pid ∈ cursorSelected d ctx, d.peers[pid]? = some (peers pid))
    (empty : ∀ pid ∈ cursorSelected d ctx, (peers pid).allowedipsList = [])
    (fresh : ctx.nextAllowedip = none)
    (oldResident : ∀ pid, ctx.nextPeer = some pid → ∃ p, d.peers[pid]? = some p) :
    let header := cursorHeaderSkb d ctx skb
    let state := cursorBodyState d peers ctx header
    Campaign2.Ensures (wgGetDeviceDump ctx prev skb) (fun s => s.wg.device = some d)
      (fun result s => result = cursorCallResult d (2 + if prev != 0 && prev != d.deviceUpdateGen then 16 else 0)
          (if ctx.nextPeer.isNone then deviceFixedAttrs d else [])
          state.1 state.2.1 state.2.2.1 state.2.2.2.1 state.2.2.2.2 ∧
        s.wg.device = some (cursorReleased (cursorAcquired d (if state.2.2.2.1 then none else state.2.1)) state.1.nextPeer)) := by
  dsimp only
  have body := cursorDumpBody_normal d peers ctx residents empty fresh oldResident
    (2 + if prev != 0 && prev != d.deviceUpdateGen then 16 else 0)
    (if ctx.nextPeer.isNone then deviceFixedAttrs d else []) (cursorHeaderSkb d ctx skb)
  have header := cursorHeader_normal d ctx prev skb (cursorDumpBody d ctx) _ _ body
  intro g ambient result final after device run
  change g.dev = some d at device
  rw [wgGetDeviceDump_cursor_factor] at run
  simp [getDev,device] at run
  exact header g ambient result final after device run

end Leanux.Proofs.WG.Config
