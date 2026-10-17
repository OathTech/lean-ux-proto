import Leanux.Proofs.WG.Config.DeviceDump

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- The first DATA peer carries all fixed attributes and its exact JSON entries. -/
def jsonFirstPeer (p : Peer) (ips : List Json) : PeerDumpAttrs :=
  { publicKey := hexKey p.remoteStatic
    attrs := peerFixedAttrs p ++ [("allowed_ips", Json.arr ips.toArray)]
    split := true }

/-- A continued peer carries only its identity and the next JSON entries. -/
def jsonSuffixPeer (p : Peer) (ips : List Json) : PeerDumpAttrs :=
  { publicKey := hexKey p.remoteStatic
    attrs := [("public_key", toJson (hexKey p.remoteStatic)),
      ("allowed_ips", Json.arr ips.toArray)] }

def jsonPaginationTailMessages (d : Device) (p : Peer) : List (List Json) → List NlMessage
  | [] => [.done 2 0]
  | ips :: rest =>
    .data 2 (deviceFixedAttrs d) (some [{jsonSuffixPeer p ips with split := !rest.isEmpty}]) ::
      jsonPaginationTailMessages d p rest

def jsonPaginationMessages (d : Device) (p : Peer)
    (front : List Json) (rest : List (List Json)) : List NlMessage :=
  .data 2 (deviceFixedAttrs d) (some [{jsonFirstPeer p front with split := !rest.isEmpty}]) ::
    jsonPaginationTailMessages d p rest

def jsonPaginationResult (d : Device) (p : Peer) (ips : List Json) : Json :=
  Json.mkObj (deviceFixedAttrs d ++ [("peers", Json.arr #[Json.mkObj
    (peerFixedAttrs p ++ [("allowed_ips", Json.arr ips.toArray)])])])

end Leanux.Proofs.WG.Config
