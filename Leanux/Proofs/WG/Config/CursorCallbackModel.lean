import Leanux.Proofs.WG.Config.FactoredTailModel
import Leanux.Proofs.WG.Index.ReleaseModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

def fixedPeersRun (peers : PeerId → Peer) : List PeerId → DumpCtx → Option PeerId →
    NlSkb → Array PeerDumpAttrs → DumpCtx × Option PeerId × NlSkb × Bool × Array PeerDumpAttrs
  | [],ctx,cursor,skb,prior => (ctx,cursor,skb,true,prior)
  | pid :: ids,ctx,cursor,skb,prior =>
    if peerFixedSpace (peers pid) ≤ skb.room then
      fixedPeersRun peers ids {ctx with nextAllowedip := none,allowedipsSeq := 0}
        (some pid) {skb with room := skb.room-peerFixedSpace (peers pid)}
        (prior.push {publicKey := hexKey (peers pid).remoteStatic,attrs := peerFixedAttrs (peers pid)})
    else (ctx,cursor,skb,false,prior)

def cursorAcquired (d : Device) (pid : Option PeerId) : Device :=
  match pid with
  | none => d
  | some id => match d.peers[id]? with
    | none => d
    | some p => {d with peers := d.peers.insert id {p with refcount := p.refcount+1}}

def cursorReleased (d : Device) (pid : Option PeerId) : Device :=
  match pid with
  | none => d
  | some id => match d.peers[id]? with
    | none => d
    | some p => Index.releasedPeerDevice d id p

def cursorCallResult (d : Device) (flags : Nat) (device : List (String × Json))
    (ctx : DumpCtx) (cursor : Option PeerId) (skb : NlSkb) (done : Bool)
    (peers : Option (Array PeerDumpAttrs)) : DumpCall :=
  {ret := if done then 0 else Int.ofNat (NLMSG_GOODSIZE-skb.room),
   skb := {skb with messages := skb.messages ++ [.data flags device (peers.map (·.toList))]},
   ctx := {ctx with nextPeer := if done then none else cursor},prevSeq := d.deviceUpdateGen}

def cursorSelected (d : Device) (ctx : DumpCtx) : List PeerId :=
  match ctx.nextPeer with
  | none => d.peerList
  | some pid => (d.peerList.dropWhile (· != pid)).drop 1

def cursorGuardValue (d : Device) (ctx : DumpCtx) : Bool :=
  d.peerList.isEmpty || ((ctx.nextPeer.bind fun pid => d.peers[pid]?).map (·.isDead)).getD false

def cursorBodyState (d : Device) (peers : PeerId → Peer) (ctx : DumpCtx) (skb : NlSkb) :
    DumpCtx × Option PeerId × NlSkb × Bool × Option (Array PeerDumpAttrs) :=
  if cursorGuardValue d ctx then (ctx,ctx.nextPeer,skb,true,none)
  else
    let state := fixedPeersRun peers (cursorSelected d ctx) ctx ctx.nextPeer skb #[]
    (state.1,state.2.1,state.2.2.1,state.2.2.2.1,some state.2.2.2.2)

end Leanux.Proofs.WG.Config
