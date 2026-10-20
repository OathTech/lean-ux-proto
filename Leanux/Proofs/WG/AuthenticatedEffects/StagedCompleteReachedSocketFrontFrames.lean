import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSocketFrontCanonical

/-! The front keeps packet identity and ownership while consuming the
original route and loopback inputs. Saved scan receipts have no native
mutation, and the final device counters are outside the packet projection. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SocketFront
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation Prepare.Points SocketInterior

theorem savedRead_framed (pid : PeerId) (p : Peer) (h : List LifetimeEvent) : Framed (savedRead pid p) w a h := by
  unfold savedRead
  prepare_framed_uncast
  exact True.intro

theorem savedAny_framed (test : Peer → Bool) (peers : List (PeerId × Peer)) (h : List LifetimeEvent) :
    Framed (savedAny test peers) w a h := by
  induction peers generalizing w a h with
  | nil=>exact True.intro
  | cons pair rest ih=>
      refine ⟨savedRead_framed _ _ _,?_⟩
      intro ignored v b middle performed
      exact boolShape_framed _ _ _ middle True.intro (ih middle)

theorem softirq_framed (h : List LifetimeEvent) : Framed softirq w a h := by
  unfold softirq
  repeat' first
    | (socket_framed_head savedAny; exact savedAny_framed _ _ _)
    | prepare_direct_frame_step

theorem loopback_framed (sites : List HiddenSite) (raised : Bool) (h : List LifetimeEvent) :
    Framed (loopback sites raised) w a h := by
  unfold loopback
  refine ⟨True.intro,?_⟩
  intro ignored v b middle performed
  apply boolShape_framed
  · exact ⟨True.intro,fun _ _ _ next _=>softirq_framed next⟩
  · exact True.intro

theorem tunnel_framed (e : Endpoint) (bytes : List UInt8) (r : Route) (exactRx : Bool) (h : List LifetimeEvent) :
    Framed (tunnel e bytes r exactRx) w a h := by
  unfold tunnel
  repeat' first
    | (socket_framed_head loopback; exact loopback_framed _ _ _)
    | prepare_direct_frame_step

theorem afterRoute_framed (e : Endpoint) (bytes : List UInt8) (ds : Nat) (exactRx : Bool)
    (result : Except Int Route) (h : List LifetimeEvent) : Framed (afterRouteShape e bytes ds exactRx result) w a h := by
  cases result with
  | error code=>exact True.intro
  | ok route=>exact ⟨tunnel_framed _ _ _ _ _,fun _ _ _ _ _=>True.intro⟩

theorem canonical_framed (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx ipv4 : Bool)
    (h : List LifetimeEvent) : Framed (canonical e cache bytes ds exactRx ipv4) w a h :=
  ⟨SocketRoute.canonical_framed _ _ _ _ _ _ _,fun result _ _ next _=>afterRoute_framed _ _ _ _ result next⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SocketFront
