import Leanux.Proofs.WG.Queues.RxCarrierState
open Leanux Leanux.WG Leanux.Proofs.WG.Queues.RxCredits
namespace Leanux.Proofs.WG.Queues.CleanupFindings
def queuedPeer : Peer :=
  {remoteStatic := [], presharedKey := [], precomputedStaticStatic := [], internalId := 1,
   refcount := 1, rxQueue := {items := [0]}}
def queuedDevice : Device :=
  {ifindex := 4, ifname := "wg0", peers := Std.TreeMap.ofList [(0, queuedPeer)]}
def queuedWorld : WGWorld := {dev := some queuedDevice}
def ambient : Ambient := {env := fun _ _ => true, timing := ⟨0,0⟩}
def isQueueStop : Bool :=
  match ((peerPut (some 0)).run queuedWorld).run ambient with
  | .error (.invariant message) =>
      message == "rcu_release: a released peer with packets on its tx_queue or rx_queue (peer.c:191)"
  | _ => false
theorem queued_positive_credit : 0 < queuedPeer.refcount := by decide
theorem queued_payment_stops : isQueueStop = true := by decide +kernel
theorem queued_payment_no_return :
    ¬ ∃ v last, ((peerPut (some 0)).run queuedWorld).run ambient = .ok (((),v),last) := by
  intro ⟨v,last,hr⟩
  have hs := queued_payment_stops
  simp only [isQueueStop,hr] at hs
  contradiction

theorem positive_credit_totality_refuted :
    ¬ (∀ (pid : PeerId) (w : WGWorld) (clock : Ambient) (d : Device) (p : Peer),
      w.dev = some d → d.peers[pid]? = some p → 0 < p.refcount →
      ∃ v last, ((peerPut (some pid)).run w).run clock = .ok (((),v),last)) := by
  intro claim
  exact queued_payment_no_return (claim 0 queuedWorld ambient queuedDevice queuedPeer
    rfl (by rfl) queued_positive_credit)

def selectedCarrier : Carrier := ⟨⟨4,0⟩,⟨4,0,1⟩,.selected⟩

theorem selected_credit_funded : Protected [selectedCarrier] [] queuedWorld := by
  intro owner
  by_cases he : owner = selectedCarrier.owner
  · subst owner
    decide +kernel
  · simp [demand,charges,Ne.symm he]

theorem selected_payment_totality_refuted :
    ¬ (∀ (c : Carrier) (cs : Ledger) (loans : Reservations) (w : WGWorld) (clock : Ambient),
      Protected (c :: cs) loans w → c.phase = .selected →
      ∃ v last, ((peerPut (some c.owner.slot)).run w).run clock = .ok (((),v),last)) := by
  intro claim
  exact queued_payment_no_return
    (claim selectedCarrier [] [] queuedWorld ambient selected_credit_funded rfl)

def cleanupPeer : Peer :=
  {remoteStatic := [], presharedKey := [], precomputedStaticStatic := [], internalId := 1,
   refcount := 1, txQueue := {items := [[0]]}}
def cleanupPacket : RxPacket :=
  {peer := 0, keypair := 0, bytes := [], source := ⟨4,0,0,0,0,0⟩}
def cleanupDevice : Device :=
  {ifindex := 4, ifname := "wg0", peers := Std.TreeMap.ofList [(0,cleanupPeer)],
   rxSkbs := Std.TreeMap.ofList [(0,cleanupPacket)],
   keypairs := Std.TreeMap.ofList [(0,({peer := some 0,refcount := 2} : Keypair))]}
def cleanupWorld : WGWorld := {dev := some cleanupDevice}

theorem cleanup_inventory : Inventory [selectedCarrier] cleanupWorld := by
  refine ⟨by simp, ?_, ?_⟩
  · intro c hc
    have he : c = selectedCarrier := by simpa using hc
    subst c
    exact ⟨rfl,cleanupPacket,rfl,rfl⟩
  · intro d id pkt hd hp
    change some cleanupDevice = some d at hd
    cases hd
    by_cases he : id = 0
    · subst id
      exact ⟨selectedCarrier,by simp,rfl⟩
    · simp [cleanupDevice,Ne.symm he] at hp

theorem cleanup_funded : Protected [selectedCarrier] [] cleanupWorld := by
  intro owner
  by_cases he : owner = selectedCarrier.owner
  · subst owner
    decide +kernel
  · simp [demand,charges,Ne.symm he]

def literalCleanup : WG.M Unit := do
  keypairPut (some cleanupPacket.keypair) false
  peerPut (some cleanupPacket.peer)
  _ ← branch .rxPollFree false
  freeRxSkb selectedCarrier.packet.slot

def cleanupStops : Bool :=
  match ((literalCleanup.run cleanupWorld).run ambient) with
  | .error (.invariant message) =>
      message == "rcu_release: a released peer with packets on its tx_queue or rx_queue (peer.c:191)"
  | _ => false

theorem cleanup_stops : cleanupStops = true := by decide +kernel
theorem cleanup_no_return :
    ¬ ∃ v last, (literalCleanup.run cleanupWorld).run ambient = .ok (((),v),last) := by
  intro ⟨v,last,hr⟩
  have hs := cleanup_stops
  simp only [cleanupStops,hr] at hs
  contradiction

theorem cleanup_key_payment_returns :
    ∃ a midway, ((keypairPut (some cleanupPacket.keypair) false).run cleanupWorld).run ambient =
      .ok (((),a),midway) := by
  have h : (((keypairPut (some cleanupPacket.keypair) false).run cleanupWorld).run ambient).isOk = true := by
    decide +kernel
  cases hr : ((keypairPut (some cleanupPacket.keypair) false).run cleanupWorld).run ambient with
  | error reason => simp [hr,Except.isOk,Except.toBool] at h
  | ok out =>
    rcases out with ⟨⟨u,a⟩,midway⟩
    cases u
    exact ⟨a,midway,rfl⟩

/-- Negation of the selected-cleanup conjunct of the historical R4 terminal,
with the original inventory, funding, packet/owner and normal-key-payment
premises, retyped to the actual WG and Ambient worlds. -/
theorem cleanup_discharge_totality_refuted :
    ¬ (∀ (c : Carrier) (cs : Ledger) (loans : Reservations)
      (w a : WGWorld) (clock midway : Ambient) (pkt : RxPacket) (pid : PeerId) (flag : Bool),
      Inventory (c :: cs) w → Protected (c :: cs) loans w → c.phase = .selected →
      packetAt w c.packet = some pkt → pkt.peer = c.owner.slot → pkt.peer = pid →
      ((keypairPut (some pkt.keypair) false).run w).run clock = .ok (((),a),midway) →
      ∃ v last, ((do keypairPut (some pkt.keypair) false; peerPut (some pid); _ ← branch .rxPollFree flag; freeRxSkb c.packet.slot : WG.M Unit).run w).run clock = .ok (((),v),last) ∧
        Inventory cs v ∧ Protected cs loans v ∧ packetAt v c.packet = none) := by
  intro claim
  obtain ⟨a,midway,hk⟩ := cleanup_key_payment_returns
  obtain ⟨v,last,hr,_⟩ := claim selectedCarrier [] [] cleanupWorld a ambient midway
    cleanupPacket 0 false cleanup_inventory cleanup_funded rfl rfl rfl rfl hk
  exact cleanup_no_return ⟨v,last,hr⟩

def unpublishedCarrier : Carrier := {selectedCarrier with phase := .unpublished}

theorem unpublished_inventory : Inventory [unpublishedCarrier] cleanupWorld := by
  refine ⟨by simp, ?_, ?_⟩
  · intro c hc
    have he : c = unpublishedCarrier := by simpa using hc
    subst c
    exact ⟨rfl,cleanupPacket,rfl,rfl⟩
  · intro d id pkt hd hp
    change some cleanupDevice = some d at hd
    cases hd
    by_cases he : id = 0
    · subst id
      exact ⟨unpublishedCarrier,by simp,rfl⟩
    · simp [cleanupDevice,Ne.symm he] at hp

theorem unpublished_funded : Protected [unpublishedCarrier] [] cleanupWorld := by
  intro owner
  by_cases he : owner = unpublishedCarrier.owner
  · subst owner
    decide +kernel
  · simp [demand,charges,Ne.symm he]

theorem unpublished_queue_owners : QueueOwners [unpublishedCarrier] cleanupWorld := by
  intro d pid p id hd hp
  change some cleanupDevice = some d at hd
  cases hd
  simp [cleanupDevice,Std.TreeMap.getElem?_insert] at hp
  obtain ⟨rfl,rfl⟩ := hp
  simp [cleanupPeer,PrevQueue.all,unpublishedCarrier]

def literalDiscard : WG.M Unit := do
  keypairPut (some cleanupPacket.keypair) false
  peerPut (some cleanupPacket.peer)
  freeRxSkb unpublishedCarrier.packet.slot

def discardStops : Bool :=
  match ((literalDiscard.run cleanupWorld).run ambient) with
  | .error (.invariant message) =>
      message == "rcu_release: a released peer with packets on its tx_queue or rx_queue (peer.c:191)"
  | _ => false

theorem discard_stops : discardStops = true := by decide +kernel

theorem discard_no_return :
    ¬ ∃ v last, (literalDiscard.run cleanupWorld).run ambient = .ok (((),v),last) := by
  intro ⟨v,last,hr⟩
  have hs := discard_stops
  simp only [discardStops,hr] at hs
  contradiction

theorem discard_unpublished_totality_refuted :
    ¬ (∀ (c : Carrier) (cs : Ledger) (loans : Reservations)
      (w a : WGWorld) (clock midway : Ambient) (pkt : RxPacket),
      Inventory (c :: cs) w → Protected (c :: cs) loans w → QueueOwners (c :: cs) w →
      c.phase = .unpublished → pkt.peer = c.owner.slot →
      ((keypairPut (some pkt.keypair) false).run w).run clock = .ok (((),a),midway) →
      ∃ v last, ((do keypairPut (some pkt.keypair) false; peerPut (some pkt.peer); freeRxSkb c.packet.slot : WG.M Unit).run w).run clock = .ok (((),v),last) ∧
        Inventory cs v ∧ Protected cs loans v ∧ QueueOwners cs v ∧ packetAt v c.packet = none) := by
  intro claim
  obtain ⟨a,midway,hk⟩ := cleanup_key_payment_returns
  obtain ⟨v,last,hr,_⟩ := claim unpublishedCarrier [] [] cleanupWorld a ambient midway
    cleanupPacket unpublished_inventory unpublished_funded unpublished_queue_owners rfl rfl hk
  exact discard_no_return ⟨v,last,hr⟩

end Leanux.Proofs.WG.Queues.CleanupFindings
