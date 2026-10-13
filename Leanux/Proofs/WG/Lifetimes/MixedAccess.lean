import Leanux.Proofs.WG.Lifetimes.Tagged
import Leanux.Proofs.WG.Keypairs.Identity

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! Concrete observations for the three families needed by receive enqueue.
Raw-reference provenance is separate from the identity actually resolved. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def getKeypairPrefix (id : KeypairId) : MixedM Keypair :=
  fun w => ExceptT.mk fun h => match (getKeypair id).run w with
    | .error e => (.error e, h)
    | .ok (k, v) => (.ok (k, v), h ++ [.keypair (.read id k.internalId)])

def setKeypairPrefix (id : KeypairId) (k : Keypair) : MixedM Unit :=
  fun w => ExceptT.mk fun h => ((setKeypair id k).run w,
    if w.k.wg.isSome then h ++ [.keypair (.write id k.internalId)] else h)

def packetStamp (w : World) (id : SkbId) : PacketStamp :=
  ((w.k.wg.map (·.ifindex)).getD 0, id + 1)

def getRxSkbPrefix (id : SkbId) : MixedM RxPacket :=
  fun w => ExceptT.mk fun h => match (getRxSkb id).run w with
    | .error e => (.error e, h)
    | .ok (p, v) => (.ok (p, v), h ++ [.packet (.read (.inr id) (packetStamp w id))])

/-- The inline update after setRxSkb's explicit getter. No device means the
original modifyDev is a no-op; there is then no write observation. -/
def writeRxSkbPrefix (id : SkbId) (p : RxPacket) : MixedM Unit :=
  fun w => ExceptT.mk fun h =>
    ((modifyDev fun d => { d with rxSkbs := d.rxSkbs.insert id p }).run w,
      if w.k.wg.isSome then h ++ [.packet (.write (.inr id) (packetStamp w id))] else h)

def setRxSkbPrefix (id : SkbId) (f : RxPacket → RxPacket) : MixedM Unit := do
  let p ← getRxSkbPrefix id
  writeRxSkbPrefix id (f p)

def getPeerMixed (id : PeerId) : MixedM Peer := peerFocus (Peers.getPeerPrefix id)
def setPeerMixed (id : PeerId) (p : Peer) : MixedM Unit := peerFocus (Peers.setPeerPrefix id p)

def peerGetLocal (id : PeerId) : PrefixM Peers.PeerEvent Unit := do
  Peers.requireNotPendingPrefix id "a reference count the handshake worker also changes"
  let p ← Peers.getPeerPrefix id
  liftPrefix (refcountInc p.refcount)
  Peers.setPeerPrefix id { p with refcount := p.refcount + 1 }

def peerGetMixed (id : PeerId) : MixedM Unit := peerFocus (peerGetLocal id)
def peerPutMixed (id : Option PeerId) : MixedM Unit := peerFocus (Peers.peerPutPrefix id)

@[simp] theorem getKeypairPrefix_run (id : KeypairId) (w : World) (h : List LifetimeEvent) :
    runPrefix (getKeypairPrefix id) w h = match (getKeypair id).run w with
      | .error e => (.error e, h)
      | .ok (k, v) => (.ok (k, v), h ++ [.keypair (.read id k.internalId)]) := rfl

@[simp] theorem setKeypairPrefix_run (id : KeypairId) (k : Keypair) (w : World) (h : List LifetimeEvent) :
    runPrefix (setKeypairPrefix id k) w h = ((setKeypair id k).run w,
      if w.k.wg.isSome then h ++ [.keypair (.write id k.internalId)] else h) := rfl

@[simp] theorem getRxSkbPrefix_run (id : SkbId) (w : World) (h : List LifetimeEvent) :
    runPrefix (getRxSkbPrefix id) w h = match (getRxSkb id).run w with
      | .error e => (.error e, h)
      | .ok (p, v) => (.ok (p, v), h ++ [.packet (.read (.inr id) (packetStamp w id))]) := rfl

theorem getKeypairPrefix_erases (id : KeypairId) :
    ErasesPrefix (getKeypairPrefix id) (getKeypair id) := by
  intro w h; rw [getKeypairPrefix_run]; cases (getKeypair id).run w <;> rfl

theorem setKeypairPrefix_erases (id : KeypairId) (k : Keypair) :
    ErasesPrefix (setKeypairPrefix id k) (setKeypair id k) := fun _ _ => rfl

theorem getRxSkbPrefix_erases (id : SkbId) :
    ErasesPrefix (getRxSkbPrefix id) (getRxSkb id) := by
  intro w h; rw [getRxSkbPrefix_run]; cases (getRxSkb id).run w <;> rfl

theorem writeRxSkbPrefix_erases (id : SkbId) (p : RxPacket) :
    ErasesPrefix (writeRxSkbPrefix id p)
      (modifyDev fun d => { d with rxSkbs := d.rxSkbs.insert id p }) := fun _ _ => rfl

theorem setRxSkbPrefix_erases (id : SkbId) (f : RxPacket → RxPacket) :
    ErasesPrefix (setRxSkbPrefix id f) (setRxSkb id f) :=
  erasesPrefix_bind (getRxSkbPrefix_erases id) (fun p => writeRxSkbPrefix_erases id (f p))

theorem peerGetLocal_erases (id : PeerId) : ErasesPrefix (peerGetLocal id) (peerGet id) :=
  erasesPrefix_bind (Peers.requireNotPendingPrefix_erases id _)
    (fun _ => erasesPrefix_bind (Peers.getPeerPrefix_erases id)
      (fun p => erasesPrefix_bind (erasesPrefix_lift _)
        (fun _ => Peers.setPeerPrefix_erases id { p with refcount := p.refcount + 1 })))

theorem getPeerMixed_erases (id : PeerId) : ErasesPrefix (getPeerMixed id) (getPeer id) :=
  peerFocus_erases (Peers.getPeerPrefix_erases id)
theorem setPeerMixed_erases (id : PeerId) (p : Peer) : ErasesPrefix (setPeerMixed id p) (setPeer id p) :=
  peerFocus_erases (Peers.setPeerPrefix_erases id p)
theorem peerGetMixed_erases (id : PeerId) : ErasesPrefix (peerGetMixed id) (peerGet id) :=
  peerFocus_erases (peerGetLocal_erases id)
theorem peerPutMixed_erases (id : Option PeerId) : ErasesPrefix (peerPutMixed id) (peerPut id) :=
  peerFocus_erases (Peers.peerPutPrefix_erases id)

theorem peerPutMixed_run (id : Option PeerId) (w : World) (h : List LifetimeEvent) :
    runPrefix (peerPutMixed id) w h =
      ((peerPut id).run w, h ++ (Peers.peerPutEvents id w).map LifetimeEvent.peer) :=
  focusPrefix_suffix _ _ _ _ _ _ _ (Peers.peerPutPrefix_run id w _)

@[simp] theorem writeRxSkbPrefix_run (id : SkbId) (p : RxPacket) (w : World) (h : List LifetimeEvent) :
    runPrefix (writeRxSkbPrefix id p) w h =
      ((modifyDev fun d => { d with rxSkbs := d.rxSkbs.insert id p }).run w,
        if w.k.wg.isSome then h ++ [.packet (.write (.inr id) (packetStamp w id))] else h) := rfl

theorem setRxSkbPrefix_run (id : SkbId) (f : RxPacket → RxPacket)
    (w : World) (h : List LifetimeEvent) :
    runPrefix (setRxSkbPrefix id f) w h = match (getRxSkb id).run w with
      | .error e => (.error e, h)
      | .ok (_, _) => ((setRxSkb id f).run w,
          h ++ [.packet (.read (.inr id) (packetStamp w id)),
                .packet (.write (.inr id) (packetStamp w id))]) := by
  unfold setRxSkbPrefix
  rw [runPrefix_bind, getRxSkbPrefix_run]
  cases hr : (getRxSkb id).run w with
  | error e => rfl
  | ok out =>
    rcases out with ⟨p, v⟩
    obtain ⟨rfl, d, hd, hp⟩ := Packets.getRxSkb_current id w v p hr
    simp only [writeRxSkbPrefix_run, hd, Option.isSome_some, ↓reduceIte]
    simp [setRxSkb, StateT.run_bind, hr, List.append_assoc]

abbrev IdentityView := Store PeerId × (KeypairId → Option Nat) × (Packets.Slot → Option PacketStamp)
def identityView (w : World) : IdentityView :=
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

theorem getPeerMixed_run (id : PeerId) (w : World) (h : List LifetimeEvent) :
    runPrefix (getPeerMixed id) w h = match (getPeer id).run w with
      | .error e => (.error e, h)
      | .ok (p, v) => (.ok (p, v), h ++ [.peer (.read id p.internalId)]) := by
  unfold getPeerMixed peerFocus
  cases hr : (getPeer id).run w with
  | error e =>
    simpa using focusPrefix_suffix LifetimeEvent.peer LifetimeEvent.peer? (Peers.getPeerPrefix id) w h _
      [] (by simp [Peers.getPeerPrefix_run, hr])
  | ok out =>
    simpa using focusPrefix_suffix LifetimeEvent.peer LifetimeEvent.peer? (Peers.getPeerPrefix id) w h _
      [.read id out.1.internalId] (by simp [Peers.getPeerPrefix_run, hr])

theorem setPeerMixed_run (id : PeerId) (p : Peer) (w : World) (h : List LifetimeEvent) :
    runPrefix (setPeerMixed id p) w h = ((setPeer id p).run w,
      if w.k.wg.isSome then h ++ [.peer (.write id p.internalId)] else h) := by
  unfold setPeerMixed peerFocus
  by_cases hd : w.k.wg.isSome
  · simpa only [hd, ↓reduceIte, List.map_cons, List.map_nil] using
      focusPrefix_suffix LifetimeEvent.peer LifetimeEvent.peer? (Peers.setPeerPrefix id p) w h _
        [.write id p.internalId] (by simp [Peers.setPeerPrefix_run, hd])
  · simpa [hd] using
      focusPrefix_suffix LifetimeEvent.peer LifetimeEvent.peer? (Peers.setPeerPrefix id p) w h _
        [] (by simp [Peers.setPeerPrefix_run, hd])

abbrev MixedSpec (P : IdentityView → Prop) (g : MixedM α)
    (Q : α → IdentityView → Prop) :=
  PrefixEnsures (fun h w => MixedInv h w ∧ P (identityView w)) LifetimeEvent.Safe g
    (fun x h w => MixedInv h w ∧ Q x (identityView w))

theorem mixed_lift (P : IdentityView → Prop) (a : M α) (ha : SameView identityView a) :
    MixedSpec P (liftPrefix a) (fun _ => P) := by
  apply PrefixEnsures.lift a (fun _ _ hi => hi.1.safe)
  intro h w x v hi hr
  have he := ha w x v hr
  exact ⟨hi.1.congr he, he ▸ hi.2⟩

theorem mixed_getKeypair (P : IdentityView → Prop) (id : KeypairId) :
    MixedSpec P (getKeypairPrefix id)
      (fun k s => P s ∧ s.2.1 id = some k.internalId) := by
  intro w h hi
  rw [getKeypairPrefix_run]
  cases hr : (getKeypair id).run w with
  | error _ => exact ⟨[], by simp, hi.1.safe, True.intro⟩
  | ok out =>
    rcases out with ⟨k, v⟩
    obtain ⟨rfl, hl⟩ := Keypairs.getKeypair_current id w v k hr
    have live : keypairResidents v id = some k.internalId := by
      have hs := congrArg (Option.map Keypairs.Cell.stamp) hl
      simpa [Keypairs.snapshot, Keypairs.cell, keypairResidents, Option.map_map, Function.comp_def] using hs
    have hn := hi.1.keyRead live
    exact ⟨[.keypair (.read id k.internalId)], rfl, hn.safe, hn, hi.2, live⟩

theorem mixed_getRxSkb (P : IdentityView → Prop) (id : SkbId) :
    MixedSpec P (getRxSkbPrefix id)
      (fun _ s => P s ∧ ∃ stamp, s.2.2 (.inr id) = some stamp) := by
  intro w h hi
  rw [getRxSkbPrefix_run]
  cases hr : (getRxSkb id).run w with
  | error _ => exact ⟨[], by simp, hi.1.safe, True.intro⟩
  | ok out =>
    rcases out with ⟨p, v⟩
    obtain ⟨rfl, d, hd, hp⟩ := Packets.getRxSkb_current id w v p hr
    have live : packetResidents v (.inr id) = some (packetStamp v id) := by
      simp [packetResidents, packetStamp, hd, hp]
    have hn := hi.1.packetRead live
    exact ⟨[.packet (.read (.inr id) (packetStamp v id))], rfl, hn.safe, hn, hi.2, _, live⟩

theorem mixed_getPeer (P : IdentityView → Prop) (id : PeerId) :
    MixedSpec P (getPeerMixed id)
      (fun p s => P s ∧ s.1.slots id = some p.internalId) := by
  intro w h hi
  rw [getPeerMixed_run]
  cases hr : (getPeer id).run w with
  | error _ => exact ⟨[], by simp, hi.1.safe, True.intro⟩
  | ok out =>
    rcases out with ⟨p, v⟩
    obtain ⟨rfl, live⟩ := Peers.getPeer_current id w v p hr
    have hn := hi.1.peerRead live
    exact ⟨[.peer (.read id p.internalId)], rfl, hn.safe, hn, hi.2, live⟩

theorem setPeer_identity (id : PeerId) (p : Peer) (w v : World)
    (live : (Peers.snapshot w).slots id = some p.internalId)
    (hr : (setPeer id p).run w = .ok ((), v)) : identityView v = identityView w := by
  have hp := Peers.setPeer_same id p w v live hr
  apply Prod.ext hp
  cases hr
  unfold identityView keypairResidents packetResidents
  simp [Option.bind_map, Function.comp_def]

theorem mixed_setPeer (P : IdentityView → Prop) (id : PeerId) (p : Peer) :
    MixedSpec (fun s => P s ∧ s.1.slots id = some p.internalId)
      (setPeerMixed id p) (fun _ => P) := by
  intro w h hi
  rw [setPeerMixed_run]
  cases hd : w.k.wg with
  | none => simp [identityView, Peers.snapshot, hd] at hi
  | some d =>
    have hr : (setPeer id p).run w = .ok ((),
        {w with k := {w.k with wg := some {d with peers := d.peers.insert id p}}}) := by
      simp [setPeer, modifyDev, modifyK, hd]
    rw [hr]
    simp only [Option.isSome_some, ↓reduceIte]
    have he := setPeer_identity id p w _ hi.2.2 hr
    have hn := (hi.1.peerWrite hi.2.2).congr he
    exact ⟨[.peer (.write id p.internalId)], rfl, hn.safe, hn, he ▸ hi.2.1⟩

end Leanux.Proofs.WG.Lifetimes
