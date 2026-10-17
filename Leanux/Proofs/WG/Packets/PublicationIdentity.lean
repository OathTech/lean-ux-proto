import Leanux.Proofs.WG.Origins.ConfiguredSession
import Leanux.Proofs.WG.Queues.RxKeyProtection

/-! Local publication certificates join actual successful decryption to its
fresh key-owner read and state publication. The configured peer is the full
historical session Context; later peer-slot allocation identity, initialized
packet transport and routing authorization are separate obligations. -/
namespace Leanux.Proofs.WG.PublicationIdentity
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open MaterialOrigin Queues Lifetimes
set_option pp.structureInstances false

theorem getRx_return (id : SkbId) (w v : WGWorld) (pkt : RxPacket)
    (ambient ambient' : Ambient)
    (hr : ((getRxSkb id).run w).run ambient = .ok ((pkt,v),ambient')) :
    v = w ∧ ambient' = ambient ∧ ∃ d, w.dev = some d ∧ d.rxSkbs[id]? = some pkt :=
  Packets.getRxSkb_current id w v pkt ambient ambient' hr

theorem deref_key (id pid : Nat) (w v : WGWorld) (ambient ambient' : Ambient)
    (hr : ((IndexOwner.peerDeref (.keypair id)).run w).run ambient = .ok ((pid,v),ambient')) :
    v = w ∧ ambient' = ambient ∧
      ∃ d k, w.dev = some d ∧ d.keypairs[id]? = some k ∧ k.peer = some pid := by
  unfold IndexOwner.peerDeref IndexOwner.peerWord at hr
  simp only [bind_assoc,pure_bind] at hr
  rw [bind_ok_ambient] at hr
  obtain ⟨key,a,aa,hkey,rest⟩ := hr
  obtain ⟨ha,haa,d,hd,hk⟩ := KeyTimes.getKeypair_return id w a key ambient aa hkey
  subst a; subst aa
  cases hp : key.peer with
  | none =>
    simp only [hp] at rest
    cases rest
  | some q =>
    simp only [hp,StateT.run_pure,CounterWindow.except_pure,
      Except.ok.injEq,Prod.mk.injEq] at rest
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := rest
    exact ⟨rfl,rfl,d,key,hd,hk,hp⟩

/-- Successful decrypt leaves the actual WG state unchanged. The rejecting
invalidation arm returns None and is not folded into this statement. -/
theorem decrypt_kernel (pkt out : RxPacket) (w v : WGWorld) (ambient ambient' : Ambient)
    (hr : ((decryptPacket pkt).run w).run ambient = .ok ((some out,v),ambient')) : v = w := by
  rw [KeyTimes.decryptPacket_factor,bind_ok_ambient] at hr
  obtain ⟨missing,a,aa,hbranch,rest⟩ := hr
  have hb : false = missing ∧ w = a ∧
      CounterWindow.record ambient .decNoKeypair false = aa := by
    simpa [branch,StateT.run_monadLift,monadLift_self,StateT.run_bind,
      StateT.run_pure,CounterWindow.except_pure,CounterWindow.branch_run,
      CounterWindow.except_ok_bind,and_assoc] using hbranch
  obtain ⟨hm,ha,haa⟩ := hb
  subst missing; subst a; subst aa
  simp only [Bool.false_eq_true,↓reduceIte] at rest
  rw [bind_ok_ambient] at rest
  obtain ⟨k,a,aa,hget,rest⟩ := rest
  obtain ⟨ha,haa,d,hd,hk⟩ := KeyTimes.getKeypair_return _ _ _ _ _ _ hget
  subst a; subst aa
  rw [bind_ok_ambient] at rest
  obtain ⟨reject,b,ab,hreject,tail⟩ := rest
  have hb := (ProjectedAction.iff_run_ambient _ _ _).mp
    (Origins.receiveReject_sameWGWorld k) w _ reject b ab hreject
  cases reject with
  | false =>
    simp only [Bool.false_eq_true,↓reduceIte] at tail
    exact ((ProjectedAction.iff_run_ambient _ _ _).mp
      (Origins.receiveTail_sameWGWorld pkt k) b ab (some out) v ambient' tail).trans hb
  | true =>
    simp only [↓reduceIte,bind_ok_ambient] at tail
    obtain ⟨fresh,c,ac,hg,u,e,ae,hs,bad⟩ := tail
    cases bad

theorem publish_factor (id : SkbId) (state : PacketState) :
    RxWorkers.publishSource id state = (do
      let pkt ← getRxSkb id
      let pid ← IndexOwner.peerDeref (.keypair pkt.keypair)
      peerGet pid
      RxCredits.publicationMiddle pid id state
      return pid) := by
  unfold RxWorkers.publishSource RxCredits.publicationMiddle
  simp only [bind_assoc]
  repeat' first
    | rfl
    | apply RxWorkers.bind_congr
    | (intro x; try dsimp only)
    | split
    | (simp only [bind_assoc]; done)

/-- Literal cached-peer setter endpoint, for either state publication. -/
theorem middle_effect (id : SkbId) (state : PacketState) (pid : PeerId)
    (w v : WGWorld) (ambient ambient' : Ambient) (d : Device) (p : Peer) (pkt : RxPacket)
    (hd : w.dev = some d) (hp : d.peers[pid]? = some p) (hpacket : d.rxSkbs[id]? = some pkt)
    (hr : ((RxCredits.publicationMiddle pid id state).run w).run ambient = .ok (((),v),ambient')) :
    v = {w with dev := some {d with rxSkbs := d.rxSkbs.insert id {pkt with state}, peers := d.peers.insert pid {p with napiScheduled := true}}} := by
  unfold RxCredits.publicationMiddle at hr
  rw [bind_ok_ambient] at hr
  obtain ⟨fresh,a,aa,hget,rest⟩ := hr
  obtain ⟨ha,haa,dev,hdev,hpeer⟩ := Origins.getPeer_return pid w a fresh ambient aa hget
  subst a; subst aa
  have he : dev = d := Option.some.inj (hdev.symm.trans hd)
  subst dev
  have he : fresh = p := Option.some.inj (hpeer.symm.trans hp)
  subst fresh
  cases contains : p.rxQueue.all.contains id with
  | false =>
    simp only [contains,Bool.not_false,↓reduceIte] at rest
    cases rest
  | true =>
    simp only [contains,Bool.not_true,Bool.false_eq_true,↓reduceIte] at rest
    rw [bind_ok_ambient] at rest
    obtain ⟨u,b,ab,hset,finish⟩ := rest
    rw [Packets.setRxSkb_run w ambient d id pkt (fun q => {q with state}) hd hpacket] at hset
    cases hset
    have result : v = {w with dev := some {d with rxSkbs := d.rxSkbs.insert id {pkt with state}, peers := d.peers.insert pid {p with napiScheduled := true}}} := by
      simpa [setPeer,modifyDev,Packets.update,hd,Except.map] using
        (congrArg (fun o => o.map (fun r => r.1.2)) finish).symm
    exact result

/-- The fresh owner read, extra peer reference, actual queue-membership guard
and state-only publication are one original normal execution. -/
theorem publish_execution (id : SkbId) (state : PacketState) (w v : WGWorld)
    (ambient ambient' : Ambient) (pid : PeerId)
    (hr : ((RxWorkers.publishSource id state).run w).run ambient = .ok ((pid,v),ambient')) :
    ∃ d pkt k p, w.dev = some d ∧ d.rxSkbs[id]? = some pkt ∧
      d.keypairs[pkt.keypair]? = some k ∧ k.peer = some pid ∧ d.peers[pid]? = some p ∧
      wgStoreView v = {wgStoreView w with dev := some {d with rxSkbs := d.rxSkbs.insert id {pkt with state}, peers := (d.peers.insert pid {p with refcount := p.refcount+1}).insert pid {p with refcount := p.refcount+1,napiScheduled := true}}} := by
  rw [publish_factor] at hr
  simp only [bind_ok_ambient] at hr
  obtain ⟨pkt,a,aa,hget,q,b,ab,hword,z,c,ac,hborrow,z',e,ae,hmid,he⟩ := hr
  cases z; cases z'
  have result : q = pid ∧ e = v ∧ ae = ambient' := by simpa [and_assoc] using he
  obtain ⟨hq,he,hae⟩ := result
  subst q; subst e; subst ae
  obtain ⟨ha,haa,d,hd,hpkt⟩ := getRx_return _ _ _ _ _ _ hget
  subst a; subst aa
  obtain ⟨hb,hab,dev,k,hdev,hk,hw⟩ := deref_key _ _ _ _ _ _ hword
  subst b; subst ab
  have ed : dev = d := Option.some.inj (hdev.symm.trans hd)
  subst dev
  obtain ⟨db,p,hdb,hp,pos,store⟩ := RxCredits.peerGet_loan pid w c ambient ac hborrow
  change w.dev = some db at hdb
  have ed : db = d := Option.some.inj (hdb.symm.trans hd)
  subst db
  have hc := congrArg WGStoreView.dev store
  change c.dev = some {d with peers := d.peers.insert pid {p with refcount := p.refcount+1}} at hc
  have effect := middle_effect id state pid c v ac ambient'
    {d with peers := d.peers.insert pid {p with refcount := p.refcount+1}}
    {p with refcount := p.refcount+1} pkt hc (by simp) hpkt hmid
  refine ⟨d,pkt,k,p,hd,hpkt,hk,hw,hp,?_⟩
  let after : Device := {d with
    rxSkbs := d.rxSkbs.insert id {pkt with state}
    peers := (d.peers.insert pid {p with refcount := p.refcount+1}).insert pid
      {p with refcount := p.refcount+1,napiScheduled := true}}
  have observed : wgStoreView v = {wgStoreView c with dev := some after} :=
    congrArg wgStoreView effect
  rw [store] at observed
  exact observed

/-- The literal successful-decrypt suffix, including its recorded branch
before payload replacement and before the first possible IRQ. -/
def Published (id : SkbId) (r : WGRunWitness (RxPacket × Option RxPacket))
    (out : RxPacket) (pid : PeerId) (v : WGWorld) (ambient : Ambient) : Prop :=
  r.Valid (RxOrigin.readDecrypt id) ∧ r.value.2 = some out ∧
  ∃ checked checkedAmbient installed installedAmbient,
    ((branch .decWorkerDecrypted true : WG.M Bool).run r.after).run r.ambientAfter =
      .ok ((true,checked),checkedAmbient) ∧
    ((setRxSkb id (fun _ => out)).run checked).run checkedAmbient =
      .ok (((),installed),installedAmbient) ∧
    ((RxWorkers.publishSource id .crypted).run installed).run installedAmbient = .ok ((pid,v),ambient)

/-- Historical configured identity, actual AEAD input/output and the stored
pre-IRQ publication endpoint, all tied to this one decrypt witness. -/
def Identity (history : List SessionOrigin.Receipt) (id : SkbId)
    (r : WGRunWitness (RxPacket × Option RxPacket)) (out : RxPacket) (pid : PeerId) (v : WGWorld) : Prop :=
  ∃ d k, r.before.dev = some d ∧ d.rxSkbs[id]? = some r.value.1 ∧
      d.keypairs[r.value.1.keypair]? = some k ∧ k.receiving.isValid = true ∧
      pid = r.value.1.peer ∧ ConfiguredSession.ByPeer history d.ifindex r.value.1.keypair k pid ∧
      out = {r.value.1 with nonce := u64le r.value.1.bytes 8,bytes := out.bytes} ∧
      aeadDecrypt k.receiving.key (counterNonce (u64le r.value.1.bytes 8))
        (r.value.1.bytes.drop 16) [] = some out.bytes ∧
      Lifetimes.packetStamp v id = Lifetimes.packetStamp r.before id ∧
      ∃ after, v.dev = some after ∧ after.ifindex = d.ifindex ∧ after.rxSkbs[id]? = some {out with state := .crypted}

/-- Actual publication names the historical configured session caller and
retains its full same-receipt material witness. It does not identify a later
peer allocation at the same raw slot. -/
theorem published_identity (history : List SessionOrigin.Receipt) (id : SkbId)
    (r : WGRunWitness (RxPacket × Option RxPacket)) (out : RxPacket) (pid : PeerId)
    (v : WGWorld) (ambient : Ambient)
    (support : ConfiguredSession.Inv history r.before) (compat : RxCredits.RxCompatible r.before)
    (published : Published id r out pid v ambient) :
    Identity history id r out pid v := by
  obtain ⟨run,output,checked,checkedAmbient,installed,installedAmbient,hbranch,hstore,hpub⟩ := published
  obtain ⟨d,k,hd,hp,hk,valid,decrypt,record,aead⟩ := RxOrigin.decrypt_receipt id r out run output
  have ka := decrypt_kernel _ _ _ _ _ _ decrypt
  have kb : checked = r.after := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.branch .decWorkerDecrypted true) (fun g => g = r.after))
    r.after r.ambientAfter true checked checkedAmbient rfl hbranch
  have hchecked : checked.dev = some d := by simp [kb,ka,hd]
  rw [Packets.setRxSkb_run checked checkedAmbient d id r.value.1 (fun _ => out) hchecked hp] at hstore
  cases hstore
  obtain ⟨pubdev,pkt,key,p,hdev,hpkt,hkey,word,hpeer,effect⟩ := publish_execution _ _ _ _ _ _ _ hpub
  have ed : pubdev = {d with rxSkbs := d.rxSkbs.insert id out} := Option.some.inj
    (hdev.symm.trans (by simp [Packets.update,hchecked]))
  subst pubdev
  have eqpkt : pkt = out := by simpa using hpkt.symm
  subst pkt
  have hfinal := congrArg WGStoreView.dev effect
  change v.dev = some _ at hfinal
  have kid : out.keypair = r.value.1.keypair := by rw [record]
  have ek : key = k := Option.some.inj (hkey.symm.trans (by simpa [kid] using hk))
  subst key
  have same : pid = r.value.1.peer := by
    have hcompat := compat d id r.value.1 hd hp d k hd hk
    rcases hcompat with h | h
    · simp [word] at h
    · exact Option.some.inj (word.symm.trans h)
  refine ⟨d,k,hd,hp,hk,valid,same,(support d hd _ k hk valid).byPeer word,record,aead,?_,?_⟩
  · simp [Lifetimes.packetStamp,hfinal,hd]
  · let after : Device := {d with
      rxSkbs := (d.rxSkbs.insert id out).insert id {out with state := .crypted}
      peers := (d.peers.insert pid {p with refcount := p.refcount+1}).insert pid
        {p with refcount := p.refcount+1,napiScheduled := true}}
    refine ⟨after,?_,rfl,?_⟩
    · simpa [after,Packets.update,hchecked] using hfinal
    · simp [after]

/-- Literal continuation after the stored decrypt. The target and source
monads stay generic, including the original arbitrary product callbacks. -/
def finishWith {m sourceM : Type → Type} [Monad m] [Monad sourceM]
    [MonadLiftT AmbientM sourceM]
    (store : SkbId → (RxPacket → RxPacket) → m Unit)
    (publish : SkbId → PacketState → m PeerId)
    (step : {α : Type} → sourceM α → m α) (id : SkbId) (pair : RxPacket × Option RxPacket) : m PeerId := do
  if ← step (branch .decWorkerDecrypted pair.2.isSome) then
    let some out := pair.2 | step (invariant "unreachable")
    store id (fun _ => out)
    publish id .crypted
  else publish id .dead

def finish (id : SkbId) (pair : RxPacket × Option RxPacket) : WG.M PeerId :=
  finishWith setRxSkb RxWorkers.publishSource (fun a => a) id pair

def selected (id : SkbId) : RxOrigin.Journal PeerId := do
  let pair ← RxOrigin.decrypt id
  finishWith (m := RxOrigin.Journal)
    (fun id f => focusStatePrefix MaterialOrigin.Event.life MaterialOrigin.life? (Lifetimes.setRxSkbPrefix id f))
    (fun id state => focusStatePrefix MaterialOrigin.Event.life MaterialOrigin.life? (RxWorkers.publishPrefix id state))
    liftWGPrefix id pair

theorem finish_erases (id : SkbId) (pair : RxPacket × Option RxPacket) :
    ErasesStatePrefix (finishWith (m := RxOrigin.Journal)
      (fun id f => focusStatePrefix MaterialOrigin.Event.life MaterialOrigin.life? (Lifetimes.setRxSkbPrefix id f))
      (fun id state => focusStatePrefix MaterialOrigin.Event.life MaterialOrigin.life? (RxWorkers.publishPrefix id state))
      liftWGPrefix id pair) (finish id pair) := by
  unfold finish finishWith
  repeat' first
    | exact focusStatePrefix_erases _ _ (Lifetimes.setRxSkbPrefix_erases _ _)
    | exact focusStatePrefix_erases _ _ (RxWorkers.publish_erases _ _)
    | exact erasesStatePrefix_lift _
    | apply erasesStatePrefix_bind
    | session_origin_intro_forall
    | split

theorem finish_published (id : SkbId) (r : WGRunWitness (RxPacket × Option RxPacket))
    (out : RxPacket) (pid : PeerId) (v : WGWorld) (ambient : Ambient)
    (valid : r.Valid (RxOrigin.readDecrypt id)) (output : r.value.2 = some out)
    (hr : ((finish id r.value).run r.after).run r.ambientAfter = .ok ((pid,v),ambient)) :
    Published id r out pid v ambient := by
  unfold finish finishWith at hr
  simp only [output,Option.isSome_some,bind_ok_ambient] at hr
  obtain ⟨b,checked,checkedAmbient,hbranch,rest⟩ := hr
  have hb : b = true := by
    simpa [branch,StateT.run_monadLift,monadLift_self,CounterWindow.branch_run,Except.map] using
      congrArg (fun o => o.map (fun r => r.1.1)) hbranch.symm
  subst b
  simp only [↓reduceIte,bind_ok_ambient] at rest
  obtain ⟨u,installed,installedAmbient,hstore,hpub⟩ := rest
  cases u
  exact ⟨valid,output,checked,checkedAmbient,installed,installedAmbient,hbranch,hstore,hpub⟩

/-- The fresh receipt is emitted by the unchanged decrypt observer before
this exact publication continuation. Older arbitrary receipts are untouched. -/
theorem selected_receipt (id : SkbId) (w v : WGWorld) (ambient ambient' : Ambient)
    (h t : List (MaterialOrigin.Event RxOrigin.Receipt)) (pid : PeerId)
    (hr : runWGPrefix (selected id) w ambient h = (.ok ((pid,v),ambient'),t)) :
    ∃ (r : WGRunWitness (RxPacket × Option RxPacket)), ∃ before tail,
      r.before = w ∧ r.ambientBefore = ambient ∧ r.Valid (RxOrigin.readDecrypt id) ∧
      runWGPrefix (focusStatePrefix MaterialOrigin.Event.life MaterialOrigin.life? (RxOrigin.readDecryptPrefix id))
        w ambient h = (.ok ((r.value,r.after),r.ambientAfter),before) ∧
      runWGPrefix (finishWith (m := RxOrigin.Journal)
        (fun id f => focusStatePrefix MaterialOrigin.Event.life MaterialOrigin.life? (Lifetimes.setRxSkbPrefix id f))
        (fun id state => focusStatePrefix MaterialOrigin.Event.life MaterialOrigin.life? (RxWorkers.publishPrefix id state))
        liftWGPrefix id r.value) r.after r.ambientAfter
        (before ++ [MaterialOrigin.Event.receipt (RxOrigin.Receipt.decrypt id r)]) = (.ok ((pid,v),ambient'),t) ∧
      t = before ++ [MaterialOrigin.Event.receipt (RxOrigin.Receipt.decrypt id r)] ++ tail ∧
      ∀ out, r.value.2 = some out → Published id r out pid v ambient' := by
  have capture := runWGPrefix_receiptWGObserved
    (focusStatePrefix MaterialOrigin.Event.life MaterialOrigin.life? (RxOrigin.readDecryptPrefix id))
    (MaterialOrigin.Event.receipt ∘ RxOrigin.Receipt.decrypt id) w ambient h
  change runStatePrefix (RxOrigin.decrypt id) w ambient h = _ at capture
  change runStatePrefix (selected id) w ambient h = _ at hr
  rw [selected,runStatePrefix_bind,capture] at hr
  cases ha : runWGPrefix
      (focusStatePrefix MaterialOrigin.Event.life MaterialOrigin.life? (RxOrigin.readDecryptPrefix id)) w ambient h with
  | mk result before =>
    rw [ha] at hr
    cases result with
    | error e => cases hr
    | ok result =>
      rcases result with ⟨⟨pair,u⟩,a⟩
      dsimp only at hr
      let r : WGRunWitness (RxPacket × Option RxPacket) := ⟨pair,w,u,ambient,a⟩
      have valid : r.Valid (RxOrigin.readDecrypt id) :=
        (focusStatePrefix_erases _ _ (RxOrigin.readDecrypt_erases id) w ambient h).symm.trans
          (congrArg Prod.fst ha)
      have ap : StateAppends (finishWith (m := RxOrigin.Journal)
          (fun id f => focusStatePrefix MaterialOrigin.Event.life MaterialOrigin.life? (Lifetimes.setRxSkbPrefix id f))
          (fun id state => focusStatePrefix MaterialOrigin.Event.life MaterialOrigin.life? (RxWorkers.publishPrefix id state))
          liftWGPrefix id pair) := by
        unfold finishWith
        repeat' first
          | exact StateAppends.focus _ _ _
          | exact StateAppends.lift _
          | apply StateAppends.bind
          | session_origin_intro_forall
          | split
      obtain ⟨tail,ht⟩ := ap u a (before ++ [MaterialOrigin.Event.receipt (RxOrigin.Receipt.decrypt id r)])
      have history := (congrArg Prod.snd hr).symm.trans ht
      refine ⟨r,before,tail,rfl,rfl,valid,rfl,hr,history,?_⟩
      intro out ho
      exact finish_published id r out pid v ambient' valid ho
        ((finish_erases id pair u a _).symm.trans (congrArg Prod.fst hr))

/-- The original observer's nonempty-ring arm calls exactly the selected cut.
The ring is the captured consume result; no ring validity premise is needed. -/
theorem prepare_factor : RxOrigin.prepare = (do
    match (← liftWGPrefix getDev).decryptQueue.consume with
    | (none,_) =>
      _ ← liftWGPrefix (branch .decWorkerConsumed false)
      return none
    | (some id,ring) =>
      _ ← liftWGPrefix (branch .decWorkerConsumed true)
      liftWGPrefix (modifyDev fun d => {d with decryptQueue := ring})
      return some (← selected id)) := by
  unfold RxOrigin.prepare RxOrigin.prepareWith selected finishWith
  simp only [bind_assoc,monadLift_self]
  apply RxWorkers.bind_congr
  intro dev
  cases hc : dev.decryptQueue.consume with
  | mk item ring =>
    cases item with
    | none => rfl
    | some id =>
      apply RxWorkers.bind_congr
      intro consumed
      apply RxWorkers.bind_congr
      intro changed
      apply RxWorkers.bind_congr
      intro pair
      rcases pair with ⟨pkt,result⟩
      apply RxWorkers.bind_congr
      intro success
      cases success
      · rfl
      · cases result with
        | none => rfl
        | some out => simp only [↓reduceIte,bind_assoc]; rfl

/-- A normal Some prepare return reaches the selected cut from this exact
captured ring item and ring write. Some alone does not assert decrypt success. -/
theorem prepare_selected (w v : WGWorld) (ambient ambient' : Ambient)
    (h t : List (MaterialOrigin.Event RxOrigin.Receipt)) (pid : PeerId)
    (hr : runWGPrefix RxOrigin.prepare w ambient h = (.ok ((some pid,v),ambient'),t)) :
    ∃ d id ring, w.dev = some d ∧ d.decryptQueue.consume = (some id,ring) ∧
      runWGPrefix (selected id) (Packets.update w (fun d => {d with decryptQueue := ring}))
        (CounterWindow.record ambient .decWorkerConsumed true) h = (.ok ((pid,v),ambient'),t) := by
  change runStatePrefix RxOrigin.prepare w ambient h = _ at hr
  rw [prepare_factor,runStatePrefix_bind] at hr
  simp only [liftWGPrefix,runStatePrefix_lift] at hr
  cases hd : w.dev with
  | none =>
    simp [getDev,hd,invariant,AmbientM.invariant] at hr
    change (Except.error _,h) = (Except.ok ((some pid,v),ambient'),t) at hr
    cases hr
  | some d =>
    have hget : (getDev.run w).run ambient = .ok ((d,w),ambient) := by simp [getDev,hd]
    rw [hget] at hr
    cases hc : d.decryptQueue.consume with
    | mk item ring =>
      cases item with
      | none =>
        simp only [hc,runStatePrefix_bind,runStatePrefix_lift,
          branch,StateT.run_monadLift,monadLift_self,StateT.run_bind,StateT.run_pure,
          CounterWindow.except_pure,CounterWindow.branch_run,CounterWindow.except_ok_bind,
          runStatePrefix_pure,Prod.mk.injEq,Except.ok.injEq] at hr
        cases hr.1.1.1
      | some id =>
        simp only [hc,runStatePrefix_bind,runStatePrefix_lift,
          branch,StateT.run_monadLift,monadLift_self,StateT.run_bind,StateT.run_pure,
          CounterWindow.except_pure,CounterWindow.branch_run,CounterWindow.except_ok_bind] at hr
        have hm : ((modifyDev (fun d => {d with decryptQueue := ring})).run w).run
            (CounterWindow.record ambient .decWorkerConsumed true) = .ok
            (((),Packets.update w (fun d => {d with decryptQueue := ring})),
              CounterWindow.record ambient .decWorkerConsumed true) := rfl
        rw [hm] at hr
        cases hs : runStatePrefix (selected id) (Packets.update w (fun d => {d with decryptQueue := ring}))
            (CounterWindow.record ambient .decWorkerConsumed true) h with
        | mk result j =>
          cases result with
          | error e => simp [hs] at hr
          | ok result =>
            rcases result with ⟨⟨p,u⟩,a⟩
            have he : p = pid ∧ u = v ∧ a = ambient' ∧ j = t := by
              simpa [hs,runStatePrefix_pure,and_assoc] using hr
            obtain ⟨rfl,rfl,rfl,rfl⟩ := he
            exact ⟨d,id,ring,rfl,hc,hs⟩

/-- Whole normal prepare, with the fresh selected decrypt receipt in its
actual journal position. Only successful decryption yields Identity; a DEAD
publication is retained without an authorization assertion. -/
theorem prepare_identity (history : List SessionOrigin.Receipt) (w v : WGWorld)
    (ambient ambient' : Ambient) (h t : List (MaterialOrigin.Event RxOrigin.Receipt)) (pid : PeerId)
    (support : ConfiguredSession.Inv history w) (compat : RxCredits.RxCompatible w)
    (hr : runWGPrefix RxOrigin.prepare w ambient h = (.ok ((some pid,v),ambient'),t)) :
    ∃ d id ring, ∃ (r : WGRunWitness (RxPacket × Option RxPacket)), ∃ pre suffix,
      w.dev = some d ∧ d.decryptQueue.consume = (some id,ring) ∧
      r.before = Packets.update w (fun d => {d with decryptQueue := ring}) ∧
      r.ambientBefore = CounterWindow.record ambient .decWorkerConsumed true ∧
      r.Valid (RxOrigin.readDecrypt id) ∧
      runWGPrefix (focusStatePrefix MaterialOrigin.Event.life MaterialOrigin.life? (RxOrigin.readDecryptPrefix id))
        r.before r.ambientBefore h = (.ok ((r.value,r.after),r.ambientAfter),h ++ pre) ∧
      t = h ++ pre ++ [MaterialOrigin.Event.receipt (RxOrigin.Receipt.decrypt id r)] ++ suffix ∧
      ∀ out, r.value.2 = some out → Identity history id r out pid v := by
  obtain ⟨d,id,ring,hd,hpop,selectedRun⟩ := prepare_selected w v ambient ambient' h t pid hr
  obtain ⟨r,before,suffix,entry,entryAmbient,valid,read,finishRun,he,success⟩ :=
    selected_receipt id _ v _ ambient' h t pid selectedRun
  let entered := Packets.update w (fun d => {d with decryptQueue := ring})
  have state : r.before.dev = some {d with decryptQueue := ring} := by
    simp [entry,Packets.update,hd]
  have hs : ConfiguredSession.Inv history r.before := by
    intro dev hdev slot k hk hv
    have eq : dev = {d with decryptQueue := ring} := Option.some.inj (hdev.symm.trans state)
    subst dev
    exact support d hd slot k hk hv
  have hc : RxCredits.RxCompatible r.before := by
    intro dev skb pkt hdev hp dev' k hdev' hk
    have eq : dev = {d with decryptQueue := ring} := Option.some.inj (hdev.symm.trans state)
    have eq' : dev' = {d with decryptQueue := ring} := Option.some.inj (hdev'.symm.trans state)
    subst dev; subst dev'
    exact compat d skb pkt hd hp d k hd hk
  obtain ⟨pre,hprefix⟩ := StateAppends.focus MaterialOrigin.Event.life MaterialOrigin.life?
    (RxOrigin.readDecryptPrefix id) entered (CounterWindow.record ambient .decWorkerConsumed true) h
  change (runWGPrefix (focusStatePrefix MaterialOrigin.Event.life MaterialOrigin.life? (RxOrigin.readDecryptPrefix id))
    entered (CounterWindow.record ambient .decWorkerConsumed true) h).2 = h ++ pre at hprefix
  rw [read] at hprefix
  change before = h ++ pre at hprefix
  refine ⟨d,id,ring,r,pre,suffix,hd,hpop,entry,entryAmbient,valid,?_,?_,?_⟩
  · simpa only [entry,entryAmbient,hprefix] using read
  · simpa only [hprefix] using he
  · intro out ho
    exact published_identity history id r out pid v ambient' hs hc (success out ho)

end Leanux.Proofs.WG.PublicationIdentity
