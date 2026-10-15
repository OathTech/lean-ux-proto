import Leanux.Proofs.WG.Origins.ConfiguredSession
import Leanux.Proofs.WG.Queues.RxKeyProtection

/-! Local publication certificates join actual successful decryption to its
fresh key-owner read and state publication. The configured peer is the full
historical session Context; later peer-slot allocation identity, initialized
packet transport and routing authorization are separate obligations. -/
namespace Leanux.Proofs.WG.PublicationIdentity
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open MaterialOrigin Queues
set_option pp.structureInstances false

theorem getRx_return (id : SkbId) (w v : World) (pkt : RxPacket)
    (hr : (getRxSkb id).run w=.ok (pkt,v)) :
    v=w ∧ ∃d,w.k.wg=some d ∧ d.rxSkbs[id]?=some pkt := by
  cases hd:w.k.wg with
  | none=>simp [getRxSkb,getDev,getK,hd,invariant] at hr
  | some d=>
    cases hp:d.rxSkbs[id]? with
    | none=>simp [getRxSkb,getDev,getK,hd,hp,invariant] at hr
    | some p=>
      have he:p=pkt ∧ w=v := by simpa [getRxSkb,getDev,getK,hd,hp] using hr
      exact ⟨he.2.symm,d,rfl,he.1 ▸ hp⟩

theorem deref_key (id pid : Nat) (w v : World)
    (hr : (IndexOwner.peerDeref (.keypair id)).run w=.ok (pid,v)) :
    v=w ∧ ∃d k,w.k.wg=some d ∧ d.keypairs[id]?=some k ∧ k.peer=some pid := by
  cases hd:w.k.wg with
  | none=>simp [IndexOwner.peerDeref,IndexOwner.peerWord,getKeypair,getDev,getK,hd,invariant] at hr
  | some d=>
    cases hk:d.keypairs[id]? with
    | none=>simp [IndexOwner.peerDeref,IndexOwner.peerWord,getKeypair,getDev,getK,hd,hk,invariant] at hr
    | some k=>
      cases hp:k.peer with
      | none=>simp [IndexOwner.peerDeref,IndexOwner.peerWord,getKeypair,getDev,getK,hd,hk,hp,unsupported] at hr
      | some q=>
        have he:q=pid ∧ w=v := by
          simpa [IndexOwner.peerDeref,IndexOwner.peerWord,getKeypair,getDev,getK,hd,hk,hp] using hr
        exact ⟨he.2.symm,d,k,rfl,hk,he.1 ▸ hp⟩

/-- Successful decrypt does not mutate the Kernel. The rejecting invalidation
arm returns None and is not folded into this statement. -/
theorem decrypt_kernel (pkt out : RxPacket) (w v : World)
    (hr : (decryptPacket pkt).run w=.ok (some out,v)) : v.k=w.k := by
  rw [KeyTimes.decryptPacket_factor] at hr
  simp only [StateT.run_bind,CounterWindow.branch_run,CounterWindow.except_ok_bind,
    Bool.false_eq_true,↓reduceIte] at hr
  cases hg:(getKeypair pkt.keypair).run (CounterWindow.record w .decNoKeypair false) with
  | error e=>simp [hg] at hr
  | ok got=>
    rcases got with ⟨k,a⟩
    obtain ⟨ha,d,hd,hk⟩:=KeyTimes.getKeypair_return _ _ _ _ hg
    subst a
    simp only [hg,CounterWindow.except_ok_bind] at hr
    cases hj:(KeyTimes.receiveReject k).run (CounterWindow.record w .decNoKeypair false) with
    | error e=>simp [hj] at hr
    | ok checked=>
      rcases checked with ⟨reject,b⟩
      have kb:=Origins.receiveReject_kernel k _ reject b hj
      cases reject with
      | false=>
        simp only [hj,CounterWindow.except_ok_bind,Bool.false_eq_true,↓reduceIte] at hr
        exact (Origins.receiveTail_kernel pkt k b (some out) v hr).trans kb
      | true=>
        simp only [hj,CounterWindow.except_ok_bind,↓reduceIte,bind_ok] at hr
        obtain ⟨fresh,c,hg,u,e,hs,bad⟩:=hr
        simp at bad

theorem publish_factor (id : SkbId) (state : PacketState) :
    RxWorkers.publishSource id state=(do
      let pkt ← getRxSkb id
      let pid ← IndexOwner.peerDeref (.keypair pkt.keypair)
      peerGet pid
      RxCredits.publicationMiddle pid id state
      return pid) := by
  unfold RxWorkers.publishSource RxCredits.publicationMiddle
  simp only [bind_assoc,pure_bind]
  repeat' first
    | rfl
    | apply RxWorkers.bind_congr
    | (intro x; try dsimp only)
    | split
    | (simp only [bind_assoc,pure_bind]; done)

/-- Literal cached-peer setter endpoint, for either state publication. -/
theorem middle_effect (id : SkbId) (state : PacketState) (pid : PeerId)
    (w v : World) (d : Device) (p : Peer) (pkt : RxPacket)
    (hd : w.k.wg=some d) (hp : d.peers[pid]?=some p) (hpacket : d.rxSkbs[id]?=some pkt)
    (hr : (RxCredits.publicationMiddle pid id state).run w=.ok ((),v)) :
    v.k={w.k with wg:=some {d with rxSkbs:=d.rxSkbs.insert id {pkt with state}, peers:=d.peers.insert pid {p with napiScheduled:=true}}} := by
  have proof : ⦃fun z=>⌜z.k=w.k⌝⦄ RxCredits.publicationMiddle pid id state
      ⦃⇓? _ z=>⌜z.k={w.k with wg:=some {d with rxSkbs:=d.rxSkbs.insert id {pkt with state}, peers:=d.peers.insert pid {p with napiScheduled:=true}}}⌝⦄ := by
    mvcgen [RxCredits.publicationMiddle,getPeer,getRxSkb,setRxSkb,getDev,getK,setPeer,modifyDev,modifyK,invariant]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all [hd,hp,hpacket]
  exact (hoare_iff_triple _ _ _).mpr proof w () v rfl hr

/-- The fresh owner read, extra peer reference, actual queue-membership guard
and state-only publication are one original normal execution. -/
theorem publish_execution (id : SkbId) (state : PacketState) (w v : World) (pid : PeerId)
    (hr : (RxWorkers.publishSource id state).run w=.ok (pid,v)) :
    ∃d pkt k p,w.k.wg=some d ∧ d.rxSkbs[id]?=some pkt ∧
      d.keypairs[pkt.keypair]?=some k ∧ k.peer=some pid ∧ d.peers[pid]?=some p ∧
      v.k={w.k with wg:=some {d with rxSkbs:=d.rxSkbs.insert id {pkt with state}, peers:=(d.peers.insert pid {p with refcount:=p.refcount+1}).insert pid {p with refcount:=p.refcount+1,napiScheduled:=true}}} := by
  rw [publish_factor,bind_ok] at hr
  obtain ⟨pkt,a,hget,q,b,hword,z,c,hborrow,z',e,hmid,he⟩ := (by simpa only [bind_ok] using hr)
  cases z; cases z'
  have result : q=pid ∧ e=v := by simpa using he
  obtain ⟨hq,he⟩:=result
  subst q; subst e
  obtain ⟨ha,d,hd,hpkt⟩:=getRx_return _ _ _ _ hget
  subst a
  obtain ⟨hb,dev,k,hdev,hk,hw⟩:=deref_key _ _ _ _ hword
  subst b
  have ed : dev=d := Option.some.inj (hdev.symm.trans hd)
  subst dev
  obtain ⟨db,p,hdb,hp,pos,hc⟩:=RxCredits.peerGet_loan pid w c hborrow
  have ed : db=d := Option.some.inj (hdb.symm.trans hd)
  subst db
  have effect:=middle_effect id state pid c v
    {d with peers:=d.peers.insert pid {p with refcount:=p.refcount+1}}
    {p with refcount:=p.refcount+1} pkt (by simp [hc]) (by simp) hpkt hmid
  refine ⟨d,pkt,k,p,hd,hpkt,hk,hw,hp,?_⟩
  simpa [hc] using effect

/-- The literal successful-decrypt suffix, including its recorded branch
before payload replacement and before the first possible IRQ. -/
def Published (id : SkbId) (r : RunWitness (RxPacket × Option RxPacket))
    (out : RxPacket) (pid : PeerId) (v : World) : Prop :=
  r.Valid (RxOrigin.readDecrypt id) ∧ r.value.2=some out ∧
  ∃checked installed,(branch .decWorkerDecrypted true).run r.after=.ok (true,checked) ∧
    (setRxSkb id (fun _=>out)).run checked=.ok ((),installed) ∧
    (RxWorkers.publishSource id .crypted).run installed=.ok (pid,v)

/-- Historical configured identity, actual AEAD input/output and the stored
pre-IRQ publication endpoint, all tied to this one decrypt witness. -/
def Identity (history : List SessionOrigin.Receipt) (id : SkbId)
    (r : RunWitness (RxPacket × Option RxPacket)) (out : RxPacket) (pid : PeerId) (v : World) : Prop :=
  ∃d k,r.before.k.wg=some d ∧ d.rxSkbs[id]?=some r.value.1 ∧
      d.keypairs[r.value.1.keypair]?=some k ∧ k.receiving.isValid=true ∧
      pid=r.value.1.peer ∧ ConfiguredSession.ByPeer history d.ifindex r.value.1.keypair k pid ∧
      out={r.value.1 with nonce:=u64le r.value.1.bytes 8,bytes:=out.bytes} ∧
      aeadDecrypt k.receiving.key (counterNonce (u64le r.value.1.bytes 8))
        (r.value.1.bytes.drop 16) []=some out.bytes ∧
      Lifetimes.packetStamp v id=Lifetimes.packetStamp r.before id ∧
      ∃after,v.k.wg=some after ∧ after.ifindex=d.ifindex ∧ after.rxSkbs[id]?=some {out with state:=.crypted}

/-- Actual publication names the historical configured session caller and
retains its full same-receipt material witness. It does not identify a later
peer allocation at the same raw slot. -/
theorem published_identity (history : List SessionOrigin.Receipt) (id : SkbId)
    (r : RunWitness (RxPacket × Option RxPacket)) (out : RxPacket) (pid : PeerId) (v : World)
    (support : ConfiguredSession.Inv history r.before) (compat : RxCredits.RxCompatible r.before)
    (published : Published id r out pid v) :
    Identity history id r out pid v := by
  obtain ⟨run,output,checked,installed,hbranch,hstore,hpub⟩:=published
  obtain ⟨d,k,hd,hp,hk,valid,decrypt,record,aead⟩:=RxOrigin.decrypt_receipt id r out run output
  have ka:=decrypt_kernel _ _ _ _ decrypt
  have kb:=sameKernel_branch .decWorkerDecrypted true _ true checked hbranch
  have hchecked : checked.k.wg=some d := by simp [kb,ka,hd]
  have store:=Packets.setRxSkb_run checked d id r.value.1 (fun _=>out) hchecked hp
  rw [store] at hstore
  cases hstore
  obtain ⟨pubdev,pkt,key,p,hdev,hpkt,hkey,word,hpeer,effect⟩:=publish_execution _ _ _ _ _ hpub
  have ed : pubdev={d with rxSkbs:=d.rxSkbs.insert id out} := Option.some.inj
    (hdev.symm.trans (by simp [Packets.update,hchecked]))
  subst pubdev
  have eqpkt : pkt=out := by simpa using hpkt.symm
  subst pkt
  have kid : out.keypair=r.value.1.keypair := by rw [record]
  have ek : key=k := Option.some.inj (hkey.symm.trans (by simpa [kid] using hk))
  subst key
  have same : pid=r.value.1.peer := by
    have hcompat:=compat d id r.value.1 hd hp d k hd hk
    rcases hcompat with h|h
    · simp [word] at h
    · exact Option.some.inj (word.symm.trans h)
  refine ⟨d,k,hd,hp,hk,valid,same,(support d hd _ k hk valid).byPeer word,record,aead,?_,?_⟩
  · simp [Lifetimes.packetStamp,effect,Packets.update,hchecked,kb,ka,hd]
  · let after : Device := {d with
      rxSkbs := (d.rxSkbs.insert id out).insert id {out with state:=.crypted}
      peers := (d.peers.insert pid {p with refcount:=p.refcount+1}).insert pid
        {p with refcount:=p.refcount+1,napiScheduled:=true}}
    refine ⟨after,?_,rfl,?_⟩
    · simpa [after,Packets.update,hchecked] using congrArg Kernel.wg effect
    · simp [after]

/-- Literal continuation after the stored decrypt. This names an existing cut,
not a replacement worker or an additional execution. -/
def finishWith {m : Type → Type} [Monad m]
    (store : SkbId → (RxPacket → RxPacket) → m Unit)
    (publish : SkbId → PacketState → m PeerId)
    (step : {α : Type} → M α → m α) (id : SkbId) (pair : RxPacket × Option RxPacket) : m PeerId := do
  if ← step (branch .decWorkerDecrypted pair.2.isSome) then
    let some out := pair.2 | step (invariant "unreachable")
    store id (fun _=>out)
    publish id .crypted
  else publish id .dead

def finish (id : SkbId) (pair : RxPacket × Option RxPacket) : M PeerId :=
  finishWith setRxSkb RxWorkers.publishSource (fun a=>a) id pair

def selected (id : SkbId) : RxOrigin.Journal PeerId := do
  let pair ← RxOrigin.decrypt id
  finishWith (m:=RxOrigin.Journal) (fun id f=>access (Lifetimes.setRxSkbPrefix id f))
    (fun id state=>access (RxWorkers.publishPrefix id state)) liftPrefix id pair

theorem finish_erases (id : SkbId) (pair : RxPacket × Option RxPacket) :
    ErasesPrefix (finishWith (m:=RxOrigin.Journal) (fun id f=>access (Lifetimes.setRxSkbPrefix id f))
      (fun id state=>access (RxWorkers.publishPrefix id state)) liftPrefix id pair) (finish id pair) := by
  unfold finish finishWith
  repeat' first
    | with_reducible exact access_erases (Lifetimes.setRxSkbPrefix_erases _ _)
    | with_reducible exact access_erases (RxWorkers.publish_erases _ _)
    | with_reducible exact erasesPrefix_lift _
    | with_reducible apply erasesPrefix_bind
    | intro_forall
    | split

theorem finish_published (id : SkbId) (r : RunWitness (RxPacket × Option RxPacket))
    (out : RxPacket) (pid : PeerId) (v : World)
    (valid : r.Valid (RxOrigin.readDecrypt id)) (output : r.value.2=some out)
    (hr : (finish id r.value).run r.after=.ok (pid,v)) : Published id r out pid v := by
  unfold finish finishWith at hr
  simp only [output,Option.isSome_some,bind_ok] at hr
  obtain ⟨b,checked,hbranch,rest⟩:=hr
  have hb : b=true := by
    have eq : true=b ∧ CounterWindow.record r.after .decWorkerDecrypted true=checked := by
      simpa [CounterWindow.branch_run] using hbranch
    exact eq.1.symm
  subst b
  simp only [↓reduceIte,bind_ok] at rest
  obtain ⟨u,installed,hstore,hpub⟩:=rest
  cases u
  exact ⟨valid,output,checked,installed,hbranch,hstore,hpub⟩

/-- The fresh receipt is emitted by the unchanged decrypt observer before
this exact publication continuation. Older arbitrary receipts are untouched. -/
theorem selected_receipt (id : SkbId) (w v : World) (h t : List (MaterialOrigin.Event RxOrigin.Receipt))
    (pid : PeerId) (hr : runPrefix (selected id) w h=(.ok (pid,v),t)) :
    ∃(r : RunWitness (RxPacket × Option RxPacket)), ∃before tail,
      r.before=w ∧ r.Valid (RxOrigin.readDecrypt id) ∧
      runPrefix (access (RxOrigin.readDecryptPrefix id)) w h=(.ok (r.value,r.after),before) ∧
      runPrefix (finishWith (m:=RxOrigin.Journal) (fun id f=>access (Lifetimes.setRxSkbPrefix id f))
        (fun id state=>access (RxWorkers.publishPrefix id state)) liftPrefix id r.value)
        r.after (before++[MaterialOrigin.Event.receipt (RxOrigin.Receipt.decrypt id r)])=(.ok (pid,v),t) ∧
      t=before++[MaterialOrigin.Event.receipt (RxOrigin.Receipt.decrypt id r)]++tail ∧
      ∀out,r.value.2=some out → Published id r out pid v := by
  rw [selected,runPrefix_bind,RxOrigin.decrypt,runPrefix_receiptObserved] at hr
  cases ha : runPrefix (access (RxOrigin.readDecryptPrefix id)) w h with
  | mk result before =>
    cases result with
    | error e=>simp [ha] at hr
    | ok result=>
      rcases result with ⟨pair,u⟩
      simp only [ha,Function.comp_apply] at hr
      let r : RunWitness (RxPacket × Option RxPacket) := ⟨pair,w,u⟩
      have valid : r.Valid (RxOrigin.readDecrypt id) :=
        (access_erases (RxOrigin.readDecrypt_erases id) w h).symm.trans (congrArg Prod.fst ha)
      have ap : Appends (finishWith (m:=RxOrigin.Journal) (fun id f=>access (Lifetimes.setRxSkbPrefix id f))
          (fun id state=>access (RxWorkers.publishPrefix id state)) liftPrefix id pair) := by
        unfold finishWith
        repeat' first
          | exact Appends.focus _ _ _
          | with_reducible exact Appends.lift _
          | with_reducible apply Appends.bind
          | intro_forall
          | split
      obtain ⟨tail,ht⟩:=ap u (before++[MaterialOrigin.Event.receipt (RxOrigin.Receipt.decrypt id r)])
      rw [hr] at ht
      refine ⟨r,before,tail,rfl,valid,rfl,hr,ht,?_⟩
      intro out ho
      exact finish_published id r out pid v valid ho
        ((finish_erases id pair u _).symm.trans (congrArg Prod.fst hr))

/-- The original observer's nonempty-ring arm calls exactly the selected cut.
The ring is the captured consume result; no ring validity premise is needed. -/
theorem prepare_factor : RxOrigin.prepare=(do
    match (← liftPrefix getDev).decryptQueue.consume with
    | (none,_)=>
      _ ← liftPrefix (branch .decWorkerConsumed false)
      return none
    | (some id,ring)=>
      _ ← liftPrefix (branch .decWorkerConsumed true)
      liftPrefix (modifyDev fun d=>{d with decryptQueue:=ring})
      return some (← selected id)) := by
  unfold RxOrigin.prepare RxOrigin.prepareWith selected finishWith
  simp only [bind_assoc,pure_bind]
  repeat' first
    | with_reducible rfl
    | with_reducible apply RxWorkers.bind_congr
    | intro_forall
    | (split <;> try simp_all only [bind_assoc,pure_bind,Option.some.injEq,Prod.mk.injEq])
    | simp only [bind_assoc,pure_bind]
    | rfl

/-- A normal Some prepare return reaches the selected cut from this exact
captured ring item and ring write. Some alone does not assert decrypt success. -/
theorem prepare_selected (w v : World) (h t : List (MaterialOrigin.Event RxOrigin.Receipt))
    (pid : PeerId) (hr : runPrefix RxOrigin.prepare w h=(.ok (some pid,v),t)) :
    ∃d id ring,w.k.wg=some d ∧ d.decryptQueue.consume=(some id,ring) ∧
      runPrefix (selected id)
        (Packets.update (CounterWindow.record w .decWorkerConsumed true) (fun d=>{d with decryptQueue:=ring})) h
        =(.ok (pid,v),t) := by
  rw [prepare_factor,runPrefix_bind,runPrefix_lift] at hr
  cases hd:w.k.wg with
  | none=>simp [getDev,getK,hd,invariant] at hr
  | some d=>
    have hget : getDev.run w=.ok (d,w) := by simp [getDev,getK,hd]
    rw [hget] at hr
    cases hc:d.decryptQueue.consume with
    | mk item ring=>
      cases item with
      | none=>
        simp only [hc,map_eq_pure_bind,runPrefix_bind,runPrefix_lift,CounterWindow.branch_run,runPrefix_pure,Prod.mk.injEq,Except.ok.injEq,Prod.mk.injEq] at hr
        cases hr.1.1
      | some id=>
        simp only [hc,runPrefix_bind,runPrefix_lift,CounterWindow.branch_run] at hr
        have hm : (modifyDev (fun d=>{d with decryptQueue:=ring})).run
            (CounterWindow.record w .decWorkerConsumed true)=.ok ((),
            Packets.update (CounterWindow.record w .decWorkerConsumed true) (fun d=>{d with decryptQueue:=ring})) := rfl
        rw [hm] at hr
        cases hs:runPrefix (selected id)
            (Packets.update (CounterWindow.record w .decWorkerConsumed true) (fun d=>{d with decryptQueue:=ring})) h with
        | mk result j=>
          cases result with
          | error e=>simp [hs] at hr
          | ok result=>
            rcases result with ⟨p,u⟩
            have he : p=pid ∧ u=v ∧ j=t := by simpa [hs,runPrefix_pure,and_assoc] using hr
            obtain ⟨rfl,rfl,rfl⟩:=he
            exact ⟨d,id,ring,rfl,hc,hs⟩

/-- Whole normal prepare, with the fresh selected decrypt receipt in its
actual journal position. Only successful decryption yields Identity; a DEAD
publication is retained without an authorization assertion. -/
theorem prepare_identity (history : List SessionOrigin.Receipt) (w v : World)
    (h t : List (MaterialOrigin.Event RxOrigin.Receipt)) (pid : PeerId)
    (support : ConfiguredSession.Inv history w) (compat : RxCredits.RxCompatible w)
    (hr : runPrefix RxOrigin.prepare w h=(.ok (some pid,v),t)) :
    ∃d id ring, ∃(r : RunWitness (RxPacket × Option RxPacket)), ∃pre suffix,
      w.k.wg=some d ∧ d.decryptQueue.consume=(some id,ring) ∧
      r.before=Packets.update (CounterWindow.record w .decWorkerConsumed true) (fun d=>{d with decryptQueue:=ring}) ∧
      r.Valid (RxOrigin.readDecrypt id) ∧
      runPrefix (access (RxOrigin.readDecryptPrefix id)) r.before h=(.ok (r.value,r.after),h++pre) ∧
      t=h++pre++[MaterialOrigin.Event.receipt (RxOrigin.Receipt.decrypt id r)]++suffix ∧
      ∀out,r.value.2=some out → Identity history id r out pid v := by
  obtain ⟨d,id,ring,hd,hpop,selectedRun⟩:=prepare_selected w v h t pid hr
  obtain ⟨r,before,suffix,entry,valid,read,finishRun,he,success⟩:=
    selected_receipt id _ v h t pid selectedRun
  let entered := Packets.update (CounterWindow.record w .decWorkerConsumed true) (fun d=>{d with decryptQueue:=ring})
  have state : r.before.k.wg=some {d with decryptQueue:=ring} := by
    simp [entry,Packets.update,hd]
  have hs : ConfiguredSession.Inv history r.before := by
    intro dev hdev slot k hk hv
    have eq : dev={d with decryptQueue:=ring} := Option.some.inj (hdev.symm.trans state)
    subst dev
    exact support d hd slot k hk hv
  have hc : RxCredits.RxCompatible r.before := by
    intro dev skb pkt hdev hp dev' k hdev' hk
    have eq : dev={d with decryptQueue:=ring} := Option.some.inj (hdev.symm.trans state)
    have eq' : dev'={d with decryptQueue:=ring} := Option.some.inj (hdev'.symm.trans state)
    subst dev; subst dev'
    exact compat d skb pkt hd hp d k hd hk
  obtain ⟨pre,hprefix⟩:=Appends.focus MaterialOrigin.Event.life MaterialOrigin.life?
    (RxOrigin.readDecryptPrefix id) entered h
  change (runPrefix (access (RxOrigin.readDecryptPrefix id)) entered h).2=h++pre at hprefix
  rw [read] at hprefix
  change before=h++pre at hprefix
  refine ⟨d,id,ring,r,pre,suffix,hd,hpop,entry,valid,?_,?_,?_⟩
  · simpa only [entry,hprefix] using read
  · simpa only [hprefix] using he
  · intro out ho; exact published_identity history id r out pid v hs hc (success out ho)

end Leanux.Proofs.WG.PublicationIdentity
