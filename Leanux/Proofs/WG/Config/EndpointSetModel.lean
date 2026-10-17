import Leanux.Proofs.WG.Config.DeviceScalars

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG

/-- The comparisons actually made by endpoint_eq; IPv6 flowinfo is absent. -/
def endpointSame (a : Endpoint) (b : Option Endpoint) : Bool :=
  let family := b.map (·.family) |>.getD 0
  let field (f : Endpoint → Nat) := b.any fun e => f e == f a
  (a.family == AF_INET && family == AF_INET && field (·.port) &&
    field (·.addr) && field (·.src) && field (·.srcIf)) ||
  (a.family == AF_INET6 && family == AF_INET6 && field (·.port) &&
    field (·.addr) && field (·.scope) && field (·.src)) ||
  (a.family == 0 && family == 0)

/-- Exact endpoint records constructed by set_peer. Other encodings are ignored. -/
def endpointAttribute (a : EndpointAttr) : Option Endpoint :=
  if a.len == 16 && a.family == AF_INET then
    some {family := a.family, addr := a.addr, port := a.port}
  else if a.len == 28 && a.family == AF_INET6 then
    some {family := a.family, addr := a.addr, port := a.port, scope := a.scope, flowinfo := a.flowinfo}
  else none

def endpointApplied (p : Peer) (a : EndpointAttr) : Peer :=
  match endpointAttribute a with
  | none => p
  | some e => if endpointSame e p.endpoint then p else {p with endpoint := some e}

/-- Preserve the actual ordered endpoint and optional reset-timestamp stores.
Resetting the timestamp does not erase the cache slot. -/
def endpointStores (d : Device) (pid : PeerId) (p : Peer) (e : Endpoint)
    (reset : Option UInt64) : Device :=
  if endpointSame e p.endpoint then d else
    let written := {p with endpoint := some e}
    let first := withPeer d pid written
    match reset with
    | none => first
    | some ts => withPeer first pid {written with dstCache := {written.dstCache with resetTs := ts}}

def endpointPeerAttrs (key : Key) (a : EndpointAttr) (updateOnly : Bool) : PeerAttrs :=
  {publicKey := some key, endpoint := some a,
    flags := if updateOnly then some WGPEER_F_UPDATE_ONLY else none}

def endpointStoredPeer (p : Peer) (e : Endpoint) (reset : Option UInt64) : Peer :=
  if endpointSame e p.endpoint then p else
    let written := {p with endpoint := some e}
    match reset with
    | none => written
    | some ts => {written with dstCache := {written.dstCache with resetTs := ts}}

def endpointAttributeStores (d : Device) (pid : PeerId) (p : Peer) (a : EndpointAttr)
    (reset : Option UInt64) : Device :=
  match endpointAttribute a with
  | none => d
  | some e => endpointStores d pid p e reset

def endpointAttributePeer (p : Peer) (a : EndpointAttr) (reset : Option UInt64) : Peer :=
  match endpointAttribute a with
  | none => p
  | some e => endpointStoredPeer p e reset

def endpointSetterDevice (d : Device) (pid : PeerId) (p : Peer) (a : EndpointAttr)
    (reset : Option UInt64) : Device :=
  let acquired := {p with refcount := p.refcount + 1}
  let configured := endpointAttributePeer acquired a reset
  withPeer (endpointAttributeStores (withPeer d pid acquired) pid acquired a reset)
    pid {configured with refcount := configured.refcount - 1}

def endpointDeviceAttrs (d : Device) (key : Key) (a : EndpointAttr) (updateOnly bad : Bool) : DeviceAttrs :=
  {device := byIndex d, peers := some ([.attrs (endpointPeerAttrs key a updateOnly)] ++
    if bad then [.malformed] else [])}

end Leanux.Proofs.WG.Config
