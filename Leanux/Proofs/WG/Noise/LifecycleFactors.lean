import Leanux.Env

/-! Native lifecycle factors. Only the open callback, the guarded keepalive
call, and the environment up callback are parameters. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.LifecycleSource
open Leanux Leanux.WG

def openWith (keepalive : PeerId → WG.M Unit) : WG.M Int := do
  let dev ← getDev
  _ ← branch .openHasInet dev.inet4Dev
  _ ← branch .openHasInet6 dev.inet6Dev
  let d ← getDev
  let ret ← socketInit d.incomingPort
  if ← branch .openSocketError (ret < 0) then return ret
  for pid in d.peerList do
    _ ← branch .openPeersIter true
    sendStagedPackets pid
    if ← branch .openKeepalive ((← getPeer pid).persistentKeepaliveInterval != 0) then keepalive pid
  _ ← branch .openPeersIter false
  return 0

theorem open_factor : WG.wgOpen = openWith WG.sendKeepalive := rfl

def upWith (openDevice : WG.M Int) : WG.M Int := do
  modifyDev fun d => { d with running := true }
  let ret ← openDevice
  if ret < 0 then modifyDev fun d => { d with running := false }
  return ret

theorem up_factor : WG.wgUp = upWith WG.wgOpen := rfl

def envUpWith (up : WG.M Int) : Leanux.M Int := do
  let some d := (← getWG).dev | return -ENODEV
  if d.running then return 0
  let ret ← up
  skipCut allocCuts
  if ret == 0 then
    Net.Fib.rtCacheFlush
    Net.Fib.netdevUp WG0_IFINDEX
  if ret == 0 then modifyEnv fun w => { w with routesPending := true }
  return ret

theorem envUp_factor : Env.wgUp = envUpWith WG.wgUp := rfl

end Leanux.Proofs.WG.Noise.LifecycleSource
