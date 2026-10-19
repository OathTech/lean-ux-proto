import Leanux.Proofs.WG.Roaming.PollAuthenticationCheckModel
import Leanux.Proofs.WG.Roaming.PollAuthenticationInitializedSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.PollAuthentication
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Queues Lifetimes PublicationIdentity
open Origins.HistorySupport (sessions)


def checkProjects (position occurrence id : Nat) (stamp : PacketStamp)
    (pkt : RxPacket) (r : RunWitness (Option Endpoint)) : Check :=
  ⟨position,occurrence,id,stamp,pkt,r.value,
    Campaign2.snapshot r.before.wg r.before.ambient,
    Campaign2.snapshot r.after.wg r.after.ambient⟩

def authenticationProjects (position : Nat)
    (decrypt : WGRunWitness (RxPacket × Option RxPacket)) (key : Keypair)
    (material : WGRunWitness (Option SessionOrigin.Context)) (ctx : SessionOrigin.Context)
    (original : Keypair) : Authentication :=
  ⟨position,Campaign2.snapshot decrypt.before decrypt.ambientBefore,decrypt.value.1,key,
    Campaign2.snapshot material.before material.ambientBefore,
    Campaign2.snapshot material.after material.ambientAfter,original,ctx⟩

def originalHistory (trace : Runner.Trace) (placeholders : Bool) : List RxHistory.Event :=
  (runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []).2

/-- Exact occurrence in the original initialized journal, including journals
whose enclosing consume or runner later stops. -/
def Check.Occurs (trace : Runner.Trace) (placeholders : Bool) (q : Check) : Prop :=
  ∃ pre post n id stamp pkt r,
    originalHistory trace placeholders = pre ++ .checkedEndpoint n id stamp pkt r :: post ∧
    q = checkProjects pre.length n id stamp pkt r

/-- The projected certificate uses the same original check and earlier decrypt.
Its configured material receipt belongs to the decrypt's strict earlier prefix. -/
def Authentication.Valid (trace : Runner.Trace) (placeholders : Bool)
    (q : Check) (e : Authentication) : Prop :=
  ∃ (pre post before after : List RxHistory.Event) (n id : Nat)
    (stamp : PacketStamp) (pkt : RxPacket) (r : RunWitness (Option Endpoint))
    (decrypt : WGRunWitness (RxPacket × Option RxPacket)) (out : RxPacket)
    (published : WGWorld) (ambient : Ambient) (key : Keypair)
    (material : WGRunWitness (Option SessionOrigin.Context)) (ctx : SessionOrigin.Context)
    (d : Device) (original : Keypair),
    originalHistory trace placeholders = pre ++ .checkedEndpoint n id stamp pkt r :: post ∧
    q = checkProjects pre.length n id stamp pkt r ∧
    r.Valid (liftWG (endpointFromSkb pkt.source)) ∧
    pre = before ++ .rx (.decrypt id decrypt) :: after ∧
    Published id decrypt out pkt.peer published ambient ∧
    Retained (sessions before) id decrypt out pkt.peer published r.before.wg ∧
    pkt = {out with state := .crypted} ∧ stamp = packetStamp published id ∧
    (decrypt.before.dev.bind fun d => d.keypairs[decrypt.value.1.keypair]?) = some key ∧
    SessionOrigin.Receipt.material pkt.peer material ∈ sessions before ∧
    material.Valid (SessionOrigin.front pkt.peer) ∧ material.value = some ctx ∧
    ConfiguredSession.Configured pkt.peer material.before ctx ∧
    material.after.dev = some d ∧ d.keypairs[ctx.slot]? = some original ∧
    MaterialOrigin.material key = MaterialOrigin.material original ∧
    e = authenticationProjects before.length decrypt key material ctx original

def extractCheck : RxHistory.Event × Nat → Option Check
  | (.checkedEndpoint n id stamp pkt r,position) =>
    some (checkProjects position n id stamp pkt r)
  | _ => none

/-- Pure projection of the one original history; no second packet execution. -/
def checks (trace : Runner.Trace) (placeholders : Bool) : List Check :=
  (originalHistory trace placeholders).zipIdx.filterMap extractCheck

def inspection (trace : Runner.Trace) (placeholders : Bool) : Inspection :=
  let run := runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []
  ⟨run.1,run.2.zipIdx.filterMap extractCheck⟩


end Leanux.Proofs.WG.Roaming.PollAuthentication
