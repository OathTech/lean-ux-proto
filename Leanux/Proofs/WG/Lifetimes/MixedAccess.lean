import Leanux.Proofs.WG.Lifetimes.Tagged
import Leanux.Proofs.WG.Keypairs.Identity

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! Concrete observations for the three families needed by receive enqueue.
Raw-reference provenance is separate from the identity actually resolved. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def getKeypairPrefix (id : KeypairId) : MixedM Keypair :=
  fun w ambient => ExceptT.mk fun h => match ((getKeypair id).run w).run ambient with
    | .error e => (.error e, h)
    | .ok ((k, v), ambient') =>
      (.ok ((k, v), ambient'), h ++ [.keypair (.read id k.internalId)])

def setKeypairPrefix (id : KeypairId) (k : Keypair) : MixedM Unit :=
  fun w ambient => ExceptT.mk fun h => (((setKeypair id k).run w).run ambient,
    if w.dev.isSome then h ++ [.keypair (.write id k.internalId)] else h)

def packetStamp (w : WGWorld) (id : SkbId) : PacketStamp :=
  ((w.dev.map (·.ifindex)).getD 0, id + 1)

def getRxSkbPrefix (id : SkbId) : MixedM RxPacket :=
  fun w ambient => ExceptT.mk fun h => match ((getRxSkb id).run w).run ambient with
    | .error e => (.error e, h)
    | .ok ((p, v), ambient') =>
      (.ok ((p, v), ambient'), h ++ [.packet (.read (.inr id) (packetStamp w id))])

/-- The inline update after setRxSkb's explicit getter. No device means the
original modifyDev is a no-op; there is then no write observation. -/
def writeRxSkbPrefix (id : SkbId) (p : RxPacket) : MixedM Unit :=
  fun w ambient => ExceptT.mk fun h =>
    (((modifyDev fun d => { d with rxSkbs := d.rxSkbs.insert id p }).run w).run ambient,
      if w.dev.isSome then h ++ [.packet (.write (.inr id) (packetStamp w id))] else h)

def setRxSkbPrefix (id : SkbId) (f : RxPacket → RxPacket) : MixedM Unit := do
  let p ← getRxSkbPrefix id
  writeRxSkbPrefix id (f p)

def getPeerMixed (id : PeerId) : MixedM Peer := peerStateFocus (Peers.getPeerPrefix id)
def setPeerMixed (id : PeerId) (p : Peer) : MixedM Unit := peerStateFocus (Peers.setPeerPrefix id p)

def peerGetLocal (id : PeerId) : WGPrefix Peers.PeerEvent Unit := do
  Peers.requireNotPendingPrefix id "a reference count the handshake worker also changes"
  let p ← Peers.getPeerPrefix id
  liftWGPrefix (refcountInc p.refcount)
  Peers.setPeerPrefix id { p with refcount := p.refcount + 1 }

def peerGetMixed (id : PeerId) : MixedM Unit := peerStateFocus (peerGetLocal id)
def peerPutMixed (id : Option PeerId) : MixedM Unit := peerStateFocus (Peers.peerPutPrefix id)

@[simp] theorem getKeypairPrefix_run (id : KeypairId) (w : WGWorld) (ambient : Ambient)
    (h : List LifetimeEvent) :
    runStatePrefix (getKeypairPrefix id) w ambient h = match ((getKeypair id).run w).run ambient with
      | .error e => (.error e, h)
      | .ok ((k, v), ambient') =>
        (.ok ((k, v), ambient'), h ++ [.keypair (.read id k.internalId)]) := rfl

@[simp] theorem setKeypairPrefix_run (id : KeypairId) (k : Keypair) (w : WGWorld)
    (ambient : Ambient) (h : List LifetimeEvent) :
    runStatePrefix (setKeypairPrefix id k) w ambient h = (((setKeypair id k).run w).run ambient,
      if w.dev.isSome then h ++ [.keypair (.write id k.internalId)] else h) := rfl

@[simp] theorem getRxSkbPrefix_run (id : SkbId) (w : WGWorld) (ambient : Ambient)
    (h : List LifetimeEvent) :
    runStatePrefix (getRxSkbPrefix id) w ambient h = match ((getRxSkb id).run w).run ambient with
      | .error e => (.error e, h)
      | .ok ((p, v), ambient') =>
        (.ok ((p, v), ambient'), h ++ [.packet (.read (.inr id) (packetStamp w id))]) := rfl

theorem getKeypairPrefix_erases (id : KeypairId) :
    ErasesStatePrefix (getKeypairPrefix id) (getKeypair id) := by
  intro w ambient h
  change (runStatePrefix (getKeypairPrefix id) w ambient h).1 = _
  rw [getKeypairPrefix_run]
  cases ((getKeypair id).run w).run ambient <;> rfl

theorem setKeypairPrefix_erases (id : KeypairId) (k : Keypair) :
    ErasesStatePrefix (setKeypairPrefix id k) (setKeypair id k) := fun _ _ _ => rfl

theorem getRxSkbPrefix_erases (id : SkbId) :
    ErasesStatePrefix (getRxSkbPrefix id) (getRxSkb id) := by
  intro w ambient h
  change (runStatePrefix (getRxSkbPrefix id) w ambient h).1 = _
  rw [getRxSkbPrefix_run]
  cases ((getRxSkb id).run w).run ambient <;> rfl

theorem writeRxSkbPrefix_erases (id : SkbId) (p : RxPacket) :
    ErasesStatePrefix (writeRxSkbPrefix id p)
      (modifyDev fun d => { d with rxSkbs := d.rxSkbs.insert id p }) := fun _ _ _ => rfl

theorem setRxSkbPrefix_erases (id : SkbId) (f : RxPacket → RxPacket) :
    ErasesStatePrefix (setRxSkbPrefix id f) (setRxSkb id f) := by
  have factor : setRxSkb id f = (do
      let p ← getRxSkb id
      modifyDev fun d => {d with rxSkbs := d.rxSkbs.insert id (f p)}) := by
    funext w ambient
    change ((setRxSkb id f).run w).run ambient =
      ((getRxSkb id >>= fun p => modifyDev fun d => {d with rxSkbs := d.rxSkbs.insert id (f p)}).run w).run ambient
    cases hd : w.dev with
    | none => simp [setRxSkb, getRxSkb, StateT.run_bind, liftSkb_run, hd, invariant, AmbientM.invariant]
    | some d =>
      cases hp : d.rxSkbs[id]? <;>
        simp [setRxSkb, getRxSkb, StateT.run_bind, liftSkb_run, SkbStore.setRx, SkbStore.getRx,
          hd, hp, modifyDev, invariant, AmbientM.invariant] <;> rfl
  rw [factor]
  exact erasesStatePrefix_bind (getRxSkbPrefix_erases id)
    (fun p => writeRxSkbPrefix_erases id (f p))

theorem peerGetLocal_erases (id : PeerId) : ErasesStatePrefix (peerGetLocal id) (peerGet id) :=
  erasesStatePrefix_bind (Peers.requireNotPendingPrefix_erases id _)
    (fun _ => erasesStatePrefix_bind (Peers.getPeerPrefix_erases id)
      (fun p => erasesStatePrefix_bind (erasesStatePrefix_lift _)
        (fun _ => Peers.setPeerPrefix_erases id { p with refcount := p.refcount + 1 })))

theorem getPeerMixed_erases (id : PeerId) : ErasesStatePrefix (getPeerMixed id) (getPeer id) :=
  focusStatePrefix_erases _ _ (Peers.getPeerPrefix_erases id)
theorem setPeerMixed_erases (id : PeerId) (p : Peer) : ErasesStatePrefix (setPeerMixed id p) (setPeer id p) :=
  focusStatePrefix_erases _ _ (Peers.setPeerPrefix_erases id p)
theorem peerGetMixed_erases (id : PeerId) : ErasesStatePrefix (peerGetMixed id) (peerGet id) :=
  focusStatePrefix_erases _ _ (peerGetLocal_erases id)
theorem peerPutMixed_erases (id : Option PeerId) : ErasesStatePrefix (peerPutMixed id) (peerPut id) :=
  focusStatePrefix_erases _ _ (Peers.peerPutPrefix_erases id)

theorem peerPutMixed_run (id : Option PeerId) (w : WGWorld) (ambient : Ambient)
    (h : List LifetimeEvent) :
    runStatePrefix (peerPutMixed id) w ambient h =
      (((peerPut id).run w).run ambient, h ++ (Peers.peerPutEvents id w).map LifetimeEvent.peer) :=
  focusPrefix_suffix _ _ _ _ _ _ _ (Peers.peerPutPrefix_run id w ambient _)

@[simp] theorem writeRxSkbPrefix_run (id : SkbId) (p : RxPacket) (w : WGWorld)
    (ambient : Ambient) (h : List LifetimeEvent) :
    runStatePrefix (writeRxSkbPrefix id p) w ambient h =
      (((modifyDev fun d => { d with rxSkbs := d.rxSkbs.insert id p }).run w).run ambient,
        if w.dev.isSome then h ++ [.packet (.write (.inr id) (packetStamp w id))] else h) := rfl

theorem setRxSkbPrefix_run (id : SkbId) (f : RxPacket → RxPacket)
    (w : WGWorld) (ambient : Ambient) (h : List LifetimeEvent) :
    runStatePrefix (setRxSkbPrefix id f) w ambient h = match ((getRxSkb id).run w).run ambient with
      | .error e => (.error e, h)
      | .ok _ => (((setRxSkb id f).run w).run ambient,
          h ++ [.packet (.read (.inr id) (packetStamp w id)),
                .packet (.write (.inr id) (packetStamp w id))]) := by
  unfold setRxSkbPrefix
  rw [runStatePrefix_bind, getRxSkbPrefix_run]
  cases hr : ((getRxSkb id).run w).run ambient with
  | error e => rfl
  | ok out =>
    rcases out with ⟨⟨p, v⟩, ambient'⟩
    obtain ⟨rfl, rfl, d, hd, hp⟩ := Packets.getRxSkb_current id w v p ambient ambient' hr
    simp only [writeRxSkbPrefix_run, hd, Option.isSome_some, ↓reduceIte]
    rw [Packets.setRxSkb_run v ambient' d id p f hd hp]
    simp [modifyDev, Packets.update, hd, List.append_assoc] <;> rfl

abbrev IdentityView := Store PeerId × (KeypairId → Option Nat) × (Packets.Slot → Option PacketStamp)
def identityView (w : WGWorld) : IdentityView :=
  (Peers.snapshot w, keypairResidents w, packetResidents w)

theorem MixedInv.congr (hi : MixedInv h w) (he : identityView v = identityView w) : MixedInv h v := by
  have hp := congrArg (fun s : IdentityView => s.1) he
  have hk := congrArg (fun s : IdentityView => s.2.1) he
  have ht := congrArg (fun s : IdentityView => s.2.2) he
  dsimp only [identityView] at hp hk ht
  exact ⟨by simpa only [Peers.AccessInv, hp] using hi.peer,
    by simpa only [hk] using hi.keypair, by simpa only [ht] using hi.packet⟩

theorem MixedInv.keyRead {id stamp : Nat} (hi : MixedInv h w)
    (hl : keypairResidents w id = some stamp) :
    MixedInv (h ++ [.keypair (.read id stamp)]) w := by
  constructor
  · simpa [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, LifetimeEvent.peer?] using hi.peer
  · simpa [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, LifetimeEvent.keypair?] using hi.keypair.read hl
  · simpa [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, LifetimeEvent.packet?] using hi.packet

theorem MixedInv.packetRead {id : Packets.Slot} {stamp : PacketStamp} (hi : MixedInv h w)
    (hl : packetResidents w id = some stamp) :
    MixedInv (h ++ [.packet (.read id stamp)]) w := by
  constructor
  · simpa [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, LifetimeEvent.peer?] using hi.peer
  · simpa [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, LifetimeEvent.keypair?] using hi.keypair
  · simpa [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, LifetimeEvent.packet?] using hi.packet.read hl

theorem MixedInv.packetWrite {id : Packets.Slot} {stamp : PacketStamp} (hi : MixedInv h w)
    (hl : packetResidents w id = some stamp) :
    MixedInv (h ++ [.packet (.write id stamp)]) w := by
  constructor
  · simpa [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, LifetimeEvent.peer?] using hi.peer
  · simpa [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, LifetimeEvent.keypair?] using hi.keypair
  · simpa [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, LifetimeEvent.packet?] using hi.packet.write hl

theorem MixedInv.peerRead {id stamp : Nat} (hi : MixedInv h w)
    (hl : (Peers.snapshot w).slots id = some stamp) :
    MixedInv (h ++ [.peer (.read id stamp)]) w := by
  constructor
  · simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, LifetimeEvent.peer?]
    exact ⟨AccessEvent.safe_append_read hi.peer.1 (fun hr => hi.peer.2.2 _ hr id hl),
      hi.peer.2.1, fun s hs => hi.peer.2.2 s (AccessEvent.released_append_read.mp hs)⟩
  · simpa [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, LifetimeEvent.keypair?] using hi.keypair
  · simpa [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, LifetimeEvent.packet?] using hi.packet

theorem MixedInv.peerWrite {id stamp : Nat} (hi : MixedInv h w)
    (hl : (Peers.snapshot w).slots id = some stamp) :
    MixedInv (h ++ [.peer (.write id stamp)]) w := by
  constructor
  · simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, LifetimeEvent.peer?]
    exact ⟨AccessEvent.safe_append_write hi.peer.1 (fun hr => hi.peer.2.2 _ hr id hl),
      hi.peer.2.1, fun s hs => hi.peer.2.2 s (AccessEvent.released_append_write.mp hs)⟩
  · simpa [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, LifetimeEvent.keypair?] using hi.keypair
  · simpa [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, LifetimeEvent.packet?] using hi.packet

theorem getPeerMixed_run (id : PeerId) (w : WGWorld) (ambient : Ambient)
    (h : List LifetimeEvent) :
    runStatePrefix (getPeerMixed id) w ambient h = match ((getPeer id).run w).run ambient with
      | .error e => (.error e, h)
      | .ok ((p, v), ambient') =>
        (.ok ((p, v), ambient'), h ++ [.peer (.read id p.internalId)]) := by
  unfold getPeerMixed peerStateFocus
  cases hr : ((getPeer id).run w).run ambient with
  | error e =>
    simpa [runStatePrefix, focusStatePrefix, StateT.run] using focusPrefix_suffix LifetimeEvent.peer LifetimeEvent.peer?
      ((Peers.getPeerPrefix id).run w) ambient h _ [] (by change runStatePrefix (Peers.getPeerPrefix id) w ambient _ = _; simp [Peers.getPeerPrefix_run, hr])
  | ok out =>
    simpa [runStatePrefix, focusStatePrefix, StateT.run] using focusPrefix_suffix LifetimeEvent.peer LifetimeEvent.peer?
      ((Peers.getPeerPrefix id).run w) ambient h _
      [.read id out.1.1.internalId] (by change runStatePrefix (Peers.getPeerPrefix id) w ambient _ = _; simp [Peers.getPeerPrefix_run, hr])

theorem setPeerMixed_run (id : PeerId) (p : Peer) (w : WGWorld) (ambient : Ambient)
    (h : List LifetimeEvent) :
    runStatePrefix (setPeerMixed id p) w ambient h = (((setPeer id p).run w).run ambient,
      if w.dev.isSome then h ++ [.peer (.write id p.internalId)] else h) := by
  unfold setPeerMixed peerStateFocus
  by_cases hd : w.dev.isSome
  · simpa only [runStatePrefix, focusStatePrefix, StateT.run, hd, ↓reduceIte, List.map_cons, List.map_nil] using
      focusPrefix_suffix LifetimeEvent.peer LifetimeEvent.peer? ((Peers.setPeerPrefix id p).run w)
        ambient h _ [.write id p.internalId] (by change runStatePrefix (Peers.setPeerPrefix id p) w ambient _ = _; simp [Peers.setPeerPrefix_run, hd] <;> rfl)
  · simpa [runStatePrefix, focusStatePrefix, StateT.run, hd] using
      focusPrefix_suffix LifetimeEvent.peer LifetimeEvent.peer? ((Peers.setPeerPrefix id p).run w)
        ambient h _ [] (by change runStatePrefix (Peers.setPeerPrefix id p) w ambient _ = _; simp [Peers.setPeerPrefix_run, hd] <;> rfl)

abbrev MixedSpec (P : IdentityView → Prop) (g : MixedM α)
    (Q : α → IdentityView → Prop) :=
  StatePrefixEnsures (fun h w _ => MixedInv h w ∧ P (identityView w)) LifetimeEvent.Safe g
    (fun x h w _ => MixedInv h w ∧ Q x (identityView w))

/-- Generic actions retain their actual state, including product callers. -/
theorem mixed_lift {S : Type} (project : S → WGWorld) (P : IdentityView → Prop)
    (a : StateT S (Except Stop) α) (ha : SameView (identityView ∘ project) a) :
    PrefixEnsures (fun h w => MixedInv h (project w) ∧ P (identityView (project w)))
      LifetimeEvent.Safe (liftPrefix a)
      (fun _ h w => MixedInv h (project w) ∧ P (identityView (project w))) := by
  apply PrefixEnsures.lift a (fun _ _ hi => hi.1.safe)
  intro h w x v hi hr
  have he := (ProjectedAction.iff_run _ _ _).mp ha w x v hr
  change identityView (project v) = identityView (project w) at he
  exact ⟨hi.1.congr he, he ▸ hi.2⟩

theorem mixed_state_lift (P : IdentityView → Prop) (a : WG.M α)
    (ha : SameView identityView a) : MixedSpec P (liftWGPrefix a) (fun _ => P) := by
  apply StatePrefixEnsures.lift a (fun _ _ _ hi => hi.1.safe)
  intro h w ambient x v ambient' hi hr
  have he := (ProjectedAction.iff_run_ambient _ _ _).mp ha w ambient x v ambient' hr
  exact ⟨hi.1.congr he, he ▸ hi.2⟩

theorem mixed_getKeypair (P : IdentityView → Prop) (id : KeypairId) :
    MixedSpec P (getKeypairPrefix id)
      (fun k s => P s ∧ s.2.1 id = some k.internalId) := by
  intro w ambient h hi
  rw [show runPrefix ((getKeypairPrefix id).run w) ambient h =
      runStatePrefix (getKeypairPrefix id) w ambient h from rfl, getKeypairPrefix_run]
  cases hr : ((getKeypair id).run w).run ambient with
  | error _ => exact ⟨[], by simp, hi.1.safe, True.intro⟩
  | ok out =>
    rcases out with ⟨⟨k, v⟩, ambient'⟩
    obtain ⟨rfl, rfl, hl⟩ := Keypairs.getKeypair_current id w v ambient ambient' k hr
    have live : keypairResidents v id = some k.internalId := by
      have hs := congrArg (Option.map Keypairs.Cell.stamp) hl
      simpa [Keypairs.snapshot, Keypairs.cell, keypairResidents, Option.map_map, Function.comp_def] using hs
    have hn := hi.1.keyRead live
    exact ⟨[.keypair (.read id k.internalId)], rfl, hn.safe, hn, hi.2, live⟩

theorem mixed_getRxSkb (P : IdentityView → Prop) (id : SkbId) :
    MixedSpec P (getRxSkbPrefix id)
      (fun _ s => P s ∧ ∃ stamp, s.2.2 (.inr id) = some stamp) := by
  intro w ambient h hi
  rw [show runPrefix ((getRxSkbPrefix id).run w) ambient h =
      runStatePrefix (getRxSkbPrefix id) w ambient h from rfl, getRxSkbPrefix_run]
  cases hr : ((getRxSkb id).run w).run ambient with
  | error _ => exact ⟨[], by simp, hi.1.safe, True.intro⟩
  | ok out =>
    rcases out with ⟨⟨p, v⟩, ambient'⟩
    obtain ⟨rfl, rfl, d, hd, hp⟩ := Packets.getRxSkb_current id w v p ambient ambient' hr
    have live : packetResidents v (.inr id) = some (packetStamp v id) := by
      simp [packetResidents, packetStamp, hd, hp]
    have hn := hi.1.packetRead live
    exact ⟨[.packet (.read (.inr id) (packetStamp v id))], rfl, hn.safe, hn, hi.2, _, live⟩

theorem mixed_getPeer (P : IdentityView → Prop) (id : PeerId) :
    MixedSpec P (getPeerMixed id)
      (fun p s => P s ∧ s.1.slots id = some p.internalId) := by
  intro w ambient h hi
  rw [show runPrefix ((getPeerMixed id).run w) ambient h =
      runStatePrefix (getPeerMixed id) w ambient h from rfl, getPeerMixed_run]
  cases hr : ((getPeer id).run w).run ambient with
  | error _ => exact ⟨[], by simp, hi.1.safe, True.intro⟩
  | ok out =>
    rcases out with ⟨⟨p, v⟩, ambient'⟩
    obtain ⟨rfl, rfl, live⟩ := Peers.getPeer_current id w v p ambient ambient' hr
    have hn := hi.1.peerRead live
    exact ⟨[.peer (.read id p.internalId)], rfl, hn.safe, hn, hi.2, live⟩

theorem setPeer_identity (id : PeerId) (p : Peer) (w v : WGWorld) (ambient ambient' : Ambient)
    (live : (Peers.snapshot w).slots id = some p.internalId)
    (hr : ((setPeer id p).run w).run ambient = .ok (((), v), ambient')) : identityView v = identityView w := by
  have hp := Peers.setPeer_same id p w v ambient ambient' live hr
  apply Prod.ext hp
  cases hr
  unfold identityView keypairResidents packetResidents
  simp [Option.bind_map, Function.comp_def]

theorem mixed_setPeer (P : IdentityView → Prop) (id : PeerId) (p : Peer) :
    MixedSpec (fun s => P s ∧ s.1.slots id = some p.internalId)
      (setPeerMixed id p) (fun _ => P) := by
  intro w ambient h hi
  rw [show runPrefix ((setPeerMixed id p).run w) ambient h =
      runStatePrefix (setPeerMixed id p) w ambient h from rfl, setPeerMixed_run]
  cases hd : w.dev with
  | none => simp [identityView, Peers.snapshot, hd] at hi
  | some d =>
    have hr : ((setPeer id p).run w).run ambient = .ok (((),
        {w with dev := some {d with peers := d.peers.insert id p}}), ambient) := by
      simp [setPeer, modifyDev, hd]
    rw [hr]
    simp only [Option.isSome_some, ↓reduceIte]
    have he := setPeer_identity id p w _ ambient ambient hi.2.2 hr
    have hn := (hi.1.peerWrite hi.2.2).congr he
    exact ⟨[.peer (.write id p.internalId)], rfl, hn.safe, hn, he ▸ hi.2.1⟩

end Leanux.Proofs.WG.Lifetimes
