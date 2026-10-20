import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedIterationPointScheduler
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePollConcrete
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNapiMetadataCanonical

/-! Fixed source atoms for NAPI, native RX polling, GRO and stack replies.
The selected packet, GRO entry and peer are arguments of their literal actions. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Napi.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

abbrev History := List Event
abbrev Result (α : Type) := Except Stop (α × World)
abbrev wg (action : WG.M α) : PrefixM Event α := liftWGObserver (liftWGPrefix action)

inductive Native : {α : Type} → PrefixM Event α → Type 1 where
  | metadata (body : WG.M α) (source : PeerMetadata.Shape body) : Native (wg body)
  | rx (body : WG.M α) (source : RxAccess.Shape body) : Native (wg body)
  | ambient : Native (liftPrefix getAmbient)
  | hiddenSite : Native (liftPrefix peekHiddenSite)
  | choose : Native (liftPrefix chooseNapiHere)
  | start : Native (liftPrefix (hidden (.sectionStart .netRx)))
  | stop : Native (liftPrefix (hidden (.sectionStop .netRx)))
  | netEnter : Native (liftPrefix (modifyAmbient fun s => {s with netRxSection := s.netRxSections}))
  | netLeave : Native (liftPrefix (modifyAmbient fun s => {s with netRxSection := 0}))
  | pending : Native (wg RxNapi.pendingSource)
  | scheduled : Native (wg RxNapi.scheduledSource)
  | branch (site : Decision) (yes : Bool) : Native (wg (branch site yes))
  | peek (pid : PeerId) : Native (wg (do (← getPeer pid).rxQueue.peek))
  | install (pid : PeerId) (queue : PrevQueue SkbId) :
      Native (wg (do setPeer pid {(← getPeer pid) with rxQueue := queue}))
  | writePeer (pid : PeerId) (queue : Peer → PrevQueue SkbId) (scheduled : Peer → Bool) :
      Native (wg (do
        let peer ← getPeer pid
        setPeer pid {peer with rxQueue := queue peer, napiScheduled := scheduled peer}))
  | ready (first : Option SkbId) : Native (wg (WG.andM (branch .rxPollPacket first.isSome) do
      let some id := first | invariant "unreachable"
      branch .rxPollNotUncrypted ((← getRxSkb id).state != .uncrypted)))
  | packet (skb : SkbId) : Native (wg (getRxSkb skb))
  | drop (pid : PeerId) : Native (wg (do
      setPeer pid {(← getPeer pid) with rxQueue := (← getPeer pid).rxQueue.dropPeeked}))
  | endpoint (source : SkbSource) : Native (wg (endpointFromSkb source))
  | keyPut (kid : KeypairId) : Native (wg (keypairPut (some kid) false))
  | free (skb : SkbId) : Native (wg (freeRxSkb skb))
  | complete (pid : PeerId) : Native (wg (do setPeer pid {(← getPeer pid) with napiScheduled := false}))
  | candidate (skb : SkbId) (packet : RxPacket) : Native (hooks.candidateEnter skb packet)
  | leave (position : Nat) : Native (hooks.candidateLeave position)
  | enter (cause : Cause) : Native (CausalScope.enterPrefix Event.scope cause)
  | exit (position : Nat) : Native (CausalScope.leavePrefix Event.scope position)
  | cut : Native (liftPrefix (skipCut ([.inetEhashSecret] ++ allocCuts)))
  | routeOutput (src dst : Nat) : Native (liftPrefix (liftWG (liftRouting (Net.routeOutput4 src dst))))
  | routeInput (src dst : Nat) : Native (liftPrefix (liftWG (liftRouting (Net.routeInput4 src dst))))
  | neighbour : Native (liftPrefix (liftWG (liftRouting (Net.neighbourClassify WG0_IFINDEX))))
  | device : Native (liftPrefix (liftWG getDev))
  | world : Native (liftPrefix getWG)
  | inbox (f : EnvWorld → EnvWorld) : Native (liftPrefix (modifyEnv f))
  | invariant (message : String) : Native (liftPrefix (Leanux.invariant message : Leanux.M α))
  | unsupported (message : String) : Native (liftPrefix (Leanux.unsupported message : Leanux.M α))
  | excluded (message : String) : Native (liftPrefix (Leanux.Env.Stack.excluded message))
  | wgInvariant (message : String) : Native (wg (invariant message : WG.M α))
  | wgUnsupported (message : String) : Native (wg (unsupported message : WG.M α))

noncomputable def metadataRemainder {α : Type} {body : WG.M α} {source : PeerMetadata.Shape body}
    {w : World} (h : History) (point : PeerMetadata.Point source w.wg w.ambient v b) : PrefixM Event α :=
  Classical.choose (point.observed_remaining h)

theorem metadataRemainder_run {α : Type} {body : WG.M α} {source : PeerMetadata.Shape body}
    {w : World} (h : History) (point : PeerMetadata.Point source w.wg w.ambient v b) :
    runPrefix (wg body) w h = runPrefix (metadataRemainder h point) {w with wg:=v,ambient:=b} h :=
  Classical.choose_spec (point.observed_remaining h)

theorem rx_observed_remaining {α : Type} {body : WG.M α} {source : RxAccess.Shape body}
    {w : World} (h : History) (point : RxAccess.Point source w.wg w.ambient v b) :
    ∃ rest : PrefixM Event α, runPrefix (wg body) w h = runPrefix rest {w with wg:=v,ambient:=b} h := by
  obtain ⟨rest,same⟩ := point.remaining
  refine ⟨liftWGObserver (liftWGPrefix rest),?_⟩
  simp only [wg,liftWGObserver_run,runWGPrefix_lift,same]

noncomputable def rxRemainder {α : Type} {body : WG.M α} {source : RxAccess.Shape body}
    {w : World} (h : History) (point : RxAccess.Point source w.wg w.ambient v b) : PrefixM Event α :=
  Classical.choose (rx_observed_remaining h point)

theorem rxRemainder_run {α : Type} {body : WG.M α} {source : RxAccess.Shape body}
    {w : World} (h : History) (point : RxAccess.Point source w.wg w.ambient v b) :
    runPrefix (wg body) w h = runPrefix (rxRemainder h point) {w with wg:=v,ambient:=b} h :=
  Classical.choose_spec (rx_observed_remaining h point)

noncomputable def freeRemainder {w : World} (h : History)
    (point : SkbAccess.Point (SkbStore.freeRx skb) w.wg w.ambient v b) : PrefixM Event Unit :=
  Classical.choose (point.observed_remaining h)

theorem freeRemainder_run {w : World} (h : History)
    (point : SkbAccess.Point (SkbStore.freeRx skb) w.wg w.ambient v b) :
    runPrefix (wg (freeRxSkb skb)) w h = runPrefix (freeRemainder h point) {w with wg:=v,ambient:=b} h :=
  Classical.choose_spec (point.observed_remaining h)

inductive Child where
  | counter (skb : SkbId) (packet : RxPacket)
  | consume (pid : PeerId) (packet : RxPacket) (endpoint : Endpoint)
  | release (peer : Option PeerId)
  | transmit (family addr : Nat) (packets : List Packet) (mtu : Nat)
  | receive6 (bytes : List UInt8)

def Child.Result : Child → Type
  | .counter _ _ => Bool
  | .consume _ _ _ => Option (List UInt8)
  | .release _ | .receive6 _ => Unit
  | .transmit _ _ _ _ => Int

def Child.action (token : Child) : PrefixM Event token.Result := match token with
  | .counter skb packet => hooks.counterCheck skb packet
  | .consume pid packet endpoint => liftWGObserver (Driver.consumeObserved hooks pid packet endpoint)
  | .release peer => liftWGObserver (hooks.peerRelease peer)
  | .transmit family addr packets mtu => liftWGObserver (Driver.transmitObserved hooks family addr packets mtu)
  | .receive6 bytes => liftPrefix (Leanux.Env.Stack.receive6 bytes)

inductive Label where
  | softirq | inlinePoll | irqExit
  | poll (pid : PeerId) (budget : Nat)
  | stack (bytes : List UInt8)
  | receive4 (bytes : List UInt8)
  | reply4 (dst : Nat) (bytes : List UInt8)
  | tagged (entry : GroOccurrence.Entry)
  | groReceive (buffer : GroOccurrence.Buffer) (entry : GroOccurrence.Entry)
  | groFlush (buffer : GroOccurrence.Buffer)

inductive Failure : {α : Type} → PrefixM Event α → Type 1 where
  | invariant (message : String) : Failure (liftPrefix (Leanux.invariant message : Leanux.M α))
  | unsupported (message : String) : Failure (liftPrefix (Leanux.unsupported message : Leanux.M α))
  | excluded (message : String) : Failure (liftPrefix (Leanux.Env.Stack.excluded message))
  | wgInvariant (message : String) : Failure (wg (invariant message : WG.M α))
  | wgUnsupported (message : String) : Failure (wg (unsupported message : WG.M α))

theorem Failure.run (failure : Failure action) (w : World) (h : History) :
    ∃ reason, runPrefix action w h = (.error reason,h) := by
  cases failure <;> exact ⟨_,rfl⟩

inductive Shape : {α : Type} → PrefixM Event α → Type 1 where
  | pure (value : α) : Shape (pure value)
  | native (token : Native action) : Shape action
  | child (token : Child) : Shape token.action
  | failed {α β : Type} {body : PrefixM Event α} (failure : Failure body) (next : α → PrefixM Event β) : Shape (body >>= next)
  | bind {body : PrefixM Event α} {next : α → PrefixM Event β}
      (head : Shape body) (tail : ∀ value, Shape (next value)) : Shape (body >>= next)
  | marked (label : Label) (body : Shape action) : Shape action

noncomputable def liftedMetadataShape (body : WG.M α) (source : PeerMetadata.Shape body) :
    Shape (liftPrefix (liftWG body)) := by
  rw [←liftWGObserver_lift]
  exact .native (.metadata body source)

noncomputable def conditionalShape (test : Prop) [Decidable test]
    {left right : PrefixM Event α} (yes : test → Shape left) (no : ¬test → Shape right) :
    Shape (if test then left else right) := by
  split
  · exact yes ‹_›
  · exact no ‹_›

noncomputable def listShape (xs : List α) (initial : σ)
    (body : α → σ → PrefixM Event (ForInStep σ)) (shapes : ∀ item acc, Shape (body item acc)) :
    Shape (forIn xs initial body) :=
  List.rec (motive := fun items => ∀ acc, Shape (forIn items acc body))
    (fun acc => .pure acc)
    (fun item rest ih acc => (List.forIn_cons body item rest acc).symm ▸
      Shape.bind (shapes item acc) (fun decision => match decision with
        | .done final => .pure final
        | .yield next => ih next)) xs initial

noncomputable def forMShape (xs : List α) (body : α → PrefixM Event Unit)
    (shapes : ∀ item, Shape (body item)) : Shape (xs.forM body) := by
  induction xs with
  | nil => exact .pure ()
  | cons item rest ih =>
    simp only [List.forM_eq_forM,List.forM_cons]
    exact .bind (shapes item) (fun _ => ih)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Napi.Points
