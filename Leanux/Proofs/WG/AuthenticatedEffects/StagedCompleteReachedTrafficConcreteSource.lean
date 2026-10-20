import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedIngressPoints

/-! Traffic dispatch follows its actual lists, worker sections and callbacks.
The receive token supplies normal endpoints; fixed ingress points expose
its allocation, admission, cleanup and counted-release source paths. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TrafficConcrete
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal Driver
abbrev History := List Event

inductive NativeKind : Type 1 where
  | base (kind : Service.Points.NativeKind)
  | route {α : Type} (body : Net.M α)
  | pending (pid : PeerId) (what : String)
  | fixture
  | sender (family dest tos : Nat) (ll : Bool)
  | packets (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts)
  | multicast (family addr : Nat)
  | drained (what : String) (flags : List Bool)
  | receive (msg : List UInt8) (src : SkbSource)

def NativeKind.Result : NativeKind → Type
  | .base kind=>kind.Result
  | @route α _=>α
  | .sender ..=>SkbSource
  | .packets ..=>Except Int (List Packet × Nat)
  | _=>Unit

def NativeKind.action (kind : NativeKind) : PrefixM Event kind.Result := match kind with
  | .base source=>source.action
  | .route body=>liftPrefix (monadLift body : Leanux.M _)
  | .pending pid what=>liftPrefix (liftWG (requireNotPending pid what))
  | .fixture=>liftPrefix Env.fixtureSend
  | .sender family dest tos ll=>liftPrefix (Env.senderSource family dest tos ll)
  | .packets family addr payload opts=>liftPrefix (Env.xmitPackets family addr payload opts)
  | .multicast family addr=>multicastObserved family addr
  | .drained what flags=>drainObserved what flags
  | .receive msg src=>receiveEntryObserved hooks msg src

def fixtureTransmit (family addr : Nat) (packets : List Packet) (mtu : Nat) : PrefixM Event Int :=
  liftWGObserver (FixtureEffects.runWith (fixtureOps hooks) (.transmit family addr packets mtu)
    (transmitObserved hooks family addr packets mtu))

inductive Shape : {α : Type} → PrefixM Event α → Type 1 where
  | pure (value : α) : Shape (pure value)
  | native (kind : NativeKind) : Shape kind.action
  | service (source : Service.Points.Shape action) : Shape action
  | poll : Shape (inlinePollObserved hooks)
  | transmit (family addr : Nat) (packets : List Packet) (mtu : Nat) : Shape (fixtureTransmit family addr packets mtu)
  | bind {body : PrefixM Event α} {next : α → PrefixM Event β}
      (head : Shape body) (tail : ∀value,Shape (next value)) : Shape (body >>= next)

noncomputable def listShape (items : List ι) (initial : σ)
    (body : ι → σ → PrefixM Event (ForInStep σ))
    (sources : ∀item acc,Shape (body item acc)) : Shape (forIn items initial body) :=
  List.rec (motive:=fun values=>∀acc,Shape (forIn values acc body))
    (fun acc=>.pure acc)
    (fun value rest ih acc=>(List.forIn_cons body value rest acc).symm ▸
      Shape.bind (sources value acc) (fun decision=>match decision with
        | .done final=>.pure final | .yield next=>ih next)) items initial

noncomputable def rangeShape (range : Std.Legacy.Range) (initial : σ)
    (body : Nat → σ → PrefixM Event (ForInStep σ))
    (sources : ∀value acc,Shape (body value acc)) : Shape (forIn range initial body) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact listShape _ _ _ sources

noncomputable def conditionalShape (test : Prop) [Decidable test]
    {yes no : PrefixM Event α} (left : test → Shape yes) (right : ¬test → Shape no) :
    Shape (if test then yes else no) := by
  split
  · exact left ‹_›
  · exact right ‹_›

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TrafficConcrete
