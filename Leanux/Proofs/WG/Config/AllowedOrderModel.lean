import Leanux.Proofs.WG.Campaign2.View
import Leanux.Proofs.WG.AllowedIps.RoutingCompletions

set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.AllowedOrder
open Leanux Leanux.WG Leanux.Proofs.WG.AllowedIps

inductive Prefix (pid : PeerId) (input : List AllowedIpEntry) :
    List AllowedIpEntry → Int → List RoutingCompletion → Prop
  | nil : Prefix pid input input 0 []
  | snoc {ip rest previous history e ret}
      (prior : Prefix pid input (.attrs ip :: rest) previous history)
      (call : e.call = .allowedIp pid ip ret) (nonnegative : 0 ≤ ret) :
      Prefix pid input rest ret (history ++ [e])

def Negative (pid : PeerId) (input : List AllowedIpEntry)
    (history : List RoutingCompletion) (ret : Int) : Prop :=
  ∃ prior ip rest previous e,
    Prefix pid input (.attrs ip :: rest) previous prior ∧
    e.call = .allowedIp pid ip ret ∧ ret < 0 ∧ history = prior ++ [e]

def Partial (pid : PeerId) (input : List AllowedIpEntry)
    (history : List RoutingCompletion) : Prop :=
  (∃ rest ret, Prefix pid input rest ret history) ∨ ∃ ret, Negative pid input history ret

def Finished (pid : PeerId) (input : List AllowedIpEntry)
    (history : List RoutingCompletion) (ret : Int) : Prop :=
  Prefix pid input [] ret history ∨
  (ret = -EINVAL ∧ ∃ rest previous,Prefix pid input (.malformed :: rest) previous history) ∨
  Negative pid input history ret

def Safe (pid : PeerId) (input : List AllowedIpEntry)
    (before history : List RoutingCompletion) : Prop :=
  ∃ added,history=before++added ∧ Partial pid input added

def At (pid : PeerId) (input rest : List AllowedIpEntry) (before : List RoutingCompletion)
    (acc : Option Int × Int) (history : List RoutingCompletion) : Prop :=
  acc.1=none ∧ ∃ added,history=before++added ∧ Prefix pid input rest acc.2 added

def Done (pid : PeerId) (input : List AllowedIpEntry) (before : List RoutingCompletion)
    (acc : Option Int × Int) (history : List RoutingCompletion) : Prop :=
  ∃ added,history=before++added ∧
    match acc.1 with
    | none => Prefix pid input [] acc.2 added
    | some ret => Finished pid input added ret

def After (pid : PeerId) (input : List AllowedIpEntry) (ip : AllowedIpAttrs)
    (rest : List AllowedIpEntry) (before : List RoutingCompletion)
    (ret : Int) (history : List RoutingCompletion) : Prop :=
  ∃ prior previous e,history=before++(prior++[e]) ∧
    Prefix pid input (.attrs ip::rest) previous prior ∧ e.call=.allowedIp pid ip ret

def Removal (peer : Option PeerId) (events : List RoutingCompletion) : Prop :=
  match peer with
  | none=>events=[]
  | some pid=>∃e,e.call=.removePeer pid∧events=[e]

def RemovalPartial (peer : Option PeerId) (events : List RoutingCompletion) : Prop :=
  events=[] ∨ Removal peer events

def Front (replace : Bool) (pid : PeerId) (events : List RoutingCompletion) : Prop :=
  if replace then Removal (some pid) events else events=[]

def UpdatePartial (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32)
    (pid : PeerId) (events : List RoutingCompletion) : Prop :=
  if flags &&& WGPEER_F_REMOVE_ME != 0 then RemovalPartial peer events
  else events=[] ∨ ∃front tail,
    Front (flags &&& WGPEER_F_REPLACE_ALLOWEDIPS != 0) pid front ∧
    Partial pid (attrs.allowedIps.getD []) tail ∧ events=front++tail

def UpdateFinished (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32)
    (pid : PeerId) (events : List RoutingCompletion) (ret : Int) : Prop :=
  if flags &&& WGPEER_F_REMOVE_ME != 0 then ret=0∧Removal peer events
  else ∃front tail,
    Front (flags &&& WGPEER_F_REPLACE_ALLOWEDIPS != 0) pid front ∧
    Finished pid (attrs.allowedIps.getD []) tail ret ∧ events=front++tail

def Segment (P : List RoutingCompletion→Prop) (before history : List RoutingCompletion) :=
  ∃events,history=before++events∧P events

def eventInput (e : RoutingCompletion) : AllowedIpEntry :=
  match e.call with
  | .allowedIp _ ip _=>.attrs ip
  | _=>.malformed

def isAllowed (e : RoutingCompletion) : Bool :=
  match e.call with | .allowedIp _ _ _=>true | _=>false

def allowedEvents (events : List RoutingCompletion) : List RoutingCompletion :=
  events.filter isAllowed

structure Inspection where
  outcome : Campaign2.Outcome Int
  completions : List RoutingCompletion

def RoutedTarget (tables : FlatTable×FlatTable) (pid : PeerId)
    (entry : Campaign2.Snapshot) : Prop :=
  RoutedView (entry.wg.device.map routingState) tables ∧
  RoutingResident pid (entry.wg.device.map routingState)

def RoutedFacts (tables : FlatTable×FlatTable) (result : Inspection) : Prop :=
  CompletionSafe tables result.completions ∧
  match result.outcome with
  | .error _=>True
  | .ok (_,final)=>RoutedView (final.wg.device.map routingState) (completionFold result.completions tables)

end Leanux.Proofs.WG.Config.AllowedOrder
