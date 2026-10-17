import Leanux.Proofs.WG.Queues.HolderAfterBatch

/-! An arbitrary supplied stable account is not an initialized scheduling
cut. The placeholder scheduler checks crypt queues but not a pending NAPI
peer. These findings make no initialized-reachability or kernel claim. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.PlaceholderFindings
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open DurableHolders

def peer : Peer :=
  {remoteStatic:=[],presharedKey:=[],precomputedStaticStatic:=[],
   internalId:=1,refcount:=2,rxQueue:={items:=[0]},napiScheduled:=true}
def packet : RxPacket := {peer:=0,keypair:=0,bytes:=[],state:=.crypted,source:=⟨4,0,0,0,0,0⟩}
def device : Device :=
  {ifindex:=4,ifname:="wg0",running:=true,nextPeer:=1,peerList:=[0],numPeers:=1,
   peers:=Std.TreeMap.ofList [(0,peer)],rxSkbs:=Std.TreeMap.ofList [(0,packet)],nextSkb:=1,
   decryptQueue:=PtrRing.init MAX_QUEUED_PACKETS}
def world : World :=
  {ambient:={env:=fun _ _=>true,timing:=⟨0,0⟩,hiddenPlaceholders:=true},
   tasks:=Runner.initialTasks 32,fs:=Runner.initialFS,wg:={dev:=some device}}
def owner : Owner := ⟨4,0,1⟩
def carrier : Carrier := ⟨⟨4,0⟩,owner,.queued⟩
def holders : DurableHolders := {base:=[owner]}

theorem placeholder : world.ambient.hidden=none := rfl

theorem no_worker_queue : device.handshakeQueue.empty=true ∧ device.decryptQueue.empty=true ∧
    device.encryptQueue.empty=true ∧ device.txWorkQueue=[] ∧ device.sendWorkQueue=[] := by decide +kernel

theorem scheduler_returns : ((Env.schedule none).run world).isOk=true := by decide +kernel

def pendingRx (w : World) : Bool := w.wg.dev.any fun d =>
  (d.peers[0]?).any (·.napiScheduled) && (d.rxSkbs[0]?).isSome

theorem actual_pending : (match Env.afterBatch.run world with
    | .error _ => false
    | .ok (_,v) => pendingRx v)=true := by decide +kernel

theorem afterBatch_returns : ∃ v d p pkt, Env.afterBatch.run world=.ok ((),v) ∧
    v.wg.dev=some d ∧ d.peers[0]?=some p ∧ p.napiScheduled=true ∧ d.rxSkbs[0]?=some pkt := by
  have pending := actual_pending
  cases run : Env.afterBatch.run world with
  | error e => simp only [run] at pending; cases pending
  | ok out =>
    rcases out with ⟨⟨⟩,v⟩
    cases hd : v.wg.dev with
    | none => simp only [run,pendingRx,hd,Option.any_none] at pending; cases pending
    | some d =>
      cases hp : d.peers[0]? with
      | none => simp only [run,pendingRx,hd,hp,Option.any, Bool.false_and] at pending; cases pending
      | some p =>
        cases hk : d.rxSkbs[0]? with
        | none => simp only [run,pendingRx,hd,hp,hk,Option.any,Option.isSome,Bool.and_false] at pending; cases pending
        | some pkt =>
          have napi : p.napiScheduled=true := by simpa only [run,pendingRx,hd,hp,hk,Option.any,Option.isSome,Bool.and_true] using pending
          exact ⟨v,d,p,pkt,rfl,hd,hp,napi,hk⟩

theorem still_pending : world.wg.dev=some device ∧ device.peers[0]?=some peer ∧
    peer.napiScheduled=true ∧ device.rxSkbs[0]?=some packet := ⟨rfl,rfl,rfl,rfl⟩

theorem physical : NativeRxInv 4 (PtrRing.init MAX_QUEUED_PACKETS) [] world.wg := by
  exact ⟨PtrRing.init MAX_QUEUED_PACKETS,⟨[],rfl⟩,rfl⟩

private theorem peer_at (hp : device.peers[pid]?=some p) : pid=0 ∧ p=peer := by
  change ((∅ : Std.TreeMap PeerId Peer).insert 0 peer)[pid]?=some p at hp
  simp only [Std.TreeMap.getElem?_insert] at hp
  by_cases eq : 0=pid
  · subst pid
    exact ⟨rfl,Option.some.inj hp.symm⟩
  · simp [eq] at hp

theorem inventory : Inventory [carrier] world.wg := by
  refine ⟨by simp,?_,?_⟩
  · intro c hc
    have eq : c=carrier := by simpa using hc
    subst c
    exact ⟨rfl,packet,rfl,rfl⟩
  · intro d id pkt hd hp
    change some device=some d at hd
    cases hd
    by_cases eq : id=0
    · subst id
      exact ⟨carrier,by simp,rfl⟩
    · simp [device,Ne.symm eq] at hp

theorem queues : QueueOwners [carrier] world.wg := by
  intro d pid p id hd hp
  change some device=some d at hd
  cases hd
  obtain ⟨rfl,rfl⟩ := peer_at hp
  by_cases eq : id=0
  · subst id; decide +kernel
  · simp [peer,PrevQueue.all,carrier,owner,device,Ne.symm eq]

theorem funded : Protected [carrier] holders.owners world.wg := by
  intro o
  by_cases eq : o=owner
  · subst o; decide +kernel
  · simp [demand,charges,holders,DurableHolders.owners,carrier,Ne.symm eq]

theorem keys : KeysCompatible world.wg := by
  constructor
  · intro d id pkt hd hp
    change some device=some d at hd
    cases hd
    intro other k ho hk
    change some device=some other at ho
    cases ho
    simp [device] at hk
  · intro pid d p kid hd hp current
    change some device=some d at hd
    cases hd
    obtain ⟨rfl,rfl⟩ := peer_at hp
    cases current

theorem aligned : holders.Aligned world.wg := by
  refine ⟨rfl,?_,rfl,?_,rfl,rfl⟩
  · intro d hd
    cases hd
    rfl
  · intro pid batches found
    change (device.peers[pid]?).map (fun p=>p.txQueue.all)=some batches at found
    obtain ⟨p,hp,eq⟩ := Option.map_eq_some_iff.mp found
    obtain ⟨rfl,rfl⟩ := peer_at hp
    exact eq.symm

theorem stable : StableRx [carrier] world.wg := by
  refine ⟨?_,?_,?_⟩
  · intro c hc
    have eq : c=carrier := by simpa using hc
    subst c
    rfl
  · intro d hd
    cases hd
    have empty : (PtrRing.init (α:=SkbId) MAX_QUEUED_PACKETS).items=[] := by
      simpa only [Ring.Journal.run,Ring.Journal.admitted,Ring.Journal.consumed,
        List.filterMap_nil,List.nil_append] using
        (Ring.Journal.conservation_all MAX_QUEUED_PACKETS ([] : List (Ring.Journal.Command SkbId))).symm
    have noUncrypted : uncrypted [carrier] world.wg=[] := by decide +kernel
    change ((PtrRing.init MAX_QUEUED_PACKETS).items.map fun id=>Packet.mk 4 id).Perm (uncrypted [carrier] world.wg)
    rw [empty,noUncrypted]
    exact .refl []
  · intro d pid p id hd hp cold head
    cases hd
    obtain ⟨rfl,rfl⟩ := peer_at hp
    cases cold

theorem boundary : Boundary [carrier] [] world.wg := by
  exact ⟨holders,⟨aligned,⟨inventory,queues,by simpa using funded,keys⟩⟩,stable⟩

/-- Complete durable funding and the initialized physical ring shape do not
by themselves make arbitrary-entry placeholder batch completion drain RX. -/
theorem arbitrary_completion_refuted : ¬ (∀ (cs : Ledger) (loans : Reservations) (w v : World)
    (epoch n : Nat) (h : List RxRing.Event), Boundary cs loans w.wg →
    NativeRxInv epoch (PtrRing.init n) h w.wg → w.ambient.hidden=none →
    Env.afterBatch.run w=.ok ((),v) →
    (∀ (d : Device) (id : SkbId) (pkt : RxPacket), v.wg.dev=some d → d.rxSkbs[id]?≠some pkt)) := by
  intro claim
  obtain ⟨v,d,p,pkt,run,hd,hp,napi,hpkt⟩ := afterBatch_returns
  exact claim [carrier] [] world v 4 MAX_QUEUED_PACKETS [] boundary physical placeholder run d 0 pkt hd hpkt

end Leanux.Proofs.WG.Queues.RxCredits.PlaceholderFindings
