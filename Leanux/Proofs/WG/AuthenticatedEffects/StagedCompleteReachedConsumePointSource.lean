import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNapiPointScheduler
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedReceiveMetadataCanonical

/-! Fixed original receive actions. Snapshot reads are real state reads used
only to construct the existing receipts; no new event or native effect is added. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Consume.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal
open RetirementSecurity

abbrev History := List Event
abbrev Result (α : Type) := Except Stop (α × World)
abbrev wg (action : WG.M α) : PrefixM Event α := liftWGObserver (liftWGPrefix action)

inductive Native : {α : Type} → PrefixM Event α → Type 1 where
  | metadata (body : WG.M α) (source : PeerMetadata.Shape body) : Native (wg body)
  | world : Native (liftPrefix (get : Leanux.M World))
  | branch (site : Decision) (yes : Bool) : Native (wg (branch site yes))
  | compare (site : Decision) (yes : Bool) (left right : Int) : Native (wg (branchCmp site yes left right))
  | key (kid : KeypairId) : Native (wg (getKeypair kid))
  | writeKey (kid : KeypairId) (key : Keypair) : Native (wg (setKeypair kid key))
  | peer (pid : PeerId) : Native (wg (getPeer pid))
  | freshWrite (pid : PeerId) : Native (wg (do
      setPeer pid {(← getPeer pid) with sentLastminuteHandshake := true}))
  | expired (site : Decision) (birth : Int64) (limit : Nat) : Native (wg (branchExpired site birth limit))
  | previous (pid : PeerId) : Native (wg (do
      let p ← getPeer pid
      setPeer pid {p with keypairPrevious := p.keypairCurrent}))
  | current (pid : PeerId) (kid : KeypairId) : Native (wg (do
      let p ← getPeer pid
      setPeer pid {p with keypairCurrent := some kid, keypairNext := none}))
  | statsDevice (len : Nat) : Native (wg (modifyDev fun d =>
      {d with rxPackets := d.rxPackets + 1, rxBytes := d.rxBytes + len}))
  | statsPeer (pid : PeerId) (len : Nat) : Native (wg (do
      let p ← getPeer pid
      setPeer pid {p with rxBytes := p.rxBytes + len}))
  | dishonest (why : Dishonest) : Native (wg (dishonest why))
  | ecn (protocol : Nat) (ds : Nat) (bytes : List UInt8) : Native (wg (inetEcnDecapsulate protocol ds bytes))
  | replay (skb : SkbId) (packet : RxPacket) (receipt : RunWitness Bool) :
      Native (emitPrefix (.old (.replay ⟨skb,packet,receipt⟩)))
  | confirmed (pid : PeerId) (kid : KeypairId) (receipt : WGRunWitness Bool) :
      Native (emitPrefix (.old (.responder (.confirmed pid kid receipt))))
  | wgInvariant (message : String) : Native (wg (invariant message : WG.M α))
  | invariant (message : String) : Native (liftPrefix (Leanux.invariant message : Leanux.M α))
  | unsupported (message : String) : Native (liftPrefix (Leanux.unsupported message : Leanux.M α))
  | excluded (message : String) : Native (liftPrefix (Leanux.Env.Stack.excluded message))
  | wgUnsupported (message : String) : Native (wg (unsupported message : WG.M α))

noncomputable def metadataRemainder {α E : Type} {body : WG.M α} {source : PeerMetadata.Shape body}
    {w : World} (h : List E) (point : PeerMetadata.Point source w.wg w.ambient v b) : PrefixM E α :=
  Classical.choose (point.observed_remaining h)

theorem metadataRemainder_run {α E : Type} {body : WG.M α} {source : PeerMetadata.Shape body}
    {w : World} (h : List E) (point : PeerMetadata.Point source w.wg w.ambient v b) :
    runPrefix (liftWGObserver (liftWGPrefix body)) w h =
      runPrefix (metadataRemainder h point) {w with wg:=v,ambient:=b} h :=
  Classical.choose_spec (point.observed_remaining h)

inductive Child where
  | endpoint (pid : PeerId) (endpoint : Endpoint)
  | keyRelease (kid : Option KeypairId)
  | handshakeTimer (pid : PeerId)
  | authenticated (pid : PeerId)
  | traversal (pid : PeerId)
  | received (pid : PeerId)
  | queued (pid : PeerId)
  | staging (pid : PeerId)
  | lookup (protocol : Nat) (bytes : List UInt8)
  | release (peer : Option PeerId)

def Child.Result : Child → Type
  | .lookup _ _ => Option PeerId
  | _ => Unit

def Child.action (token : Child) : PrefixM Event token.Result := match token with
  | .endpoint pid ep => wg (setPeerEndpoint pid ep)
  | .keyRelease kid => wg (keypairPut kid true)
  | .handshakeTimer pid => wg (timersHandshakeComplete pid .walltimeLastHandshakeData)
  | .authenticated pid => wg (timersAnyAuthenticatedPacketReceived pid)
  | .traversal pid => liftWGObserver (TimerEffects.traversalWith effects pid)
  | .received pid => liftWGObserver (TimerEffects.dataReceivedWith effects pid)
  | .queued pid => liftWGObserver (HandshakeSecurity.StagedDisposal.Effects.queuedWith effects peerRelease pid false)
  | .staging pid => liftWGObserver (Driver.stagingObserved hooks pid)
  | .lookup protocol bytes => wg (lookupSrc protocol bytes)
  | .release peer => liftWGObserver (hooks.peerRelease peer)

inductive Label where
  | counter (kid : KeypairId) (nonce : Nat)
  | counterReceipt (skb : SkbId) (packet : RxPacket)
  | confirmation (pid : PeerId) (kid : KeypairId)
  | fresh (pid : PeerId)
  | prepare (pid : PeerId) (packet : RxPacket)
  | finish (pid : PeerId) (ready : Packets.RxReady)
  | consume (pid : PeerId) (packet : RxPacket) (endpoint : Endpoint)

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

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Consume.Points
