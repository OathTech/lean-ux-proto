import Leanux.Proofs.WG.Origins.State
import Leanux.Proofs.WG.Packets.RxOriginCuts
import Leanux.Proofs.Framing.WGHandshake

/-! Local session/material and RX adapters. Incoming support is an explicit
premise about the supplied journal. These are not initialized Runner origins,
peer-public-key authorization, or proof of a prior successful Noise exchange. -/
namespace Leanux.Proofs.WG.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged MaterialOrigin Lifetimes
open Leanux.Proofs.Framing Std.Do
set_option pp.structureInstances false

theorem getPeer_return (pid : PeerId) (w v : WGWorld) (p : Peer)
    (ambient ambient' : Ambient)
    (hr : ((getPeer pid).run w).run ambient = .ok ((p, v), ambient')) :
    v = w ∧ ambient' = ambient ∧ ∃ d, w.dev = some d ∧ d.peers[pid]? = some p :=
by
  cases hd : w.dev with
  | none =>
    simp [getPeer, getDev, hd, invariant, AmbientM.invariant] at hr
    cases hr
  | some d =>
    cases hp : d.peers[pid]? with
    | none =>
      simp [getPeer, getDev, hd, hp, invariant, AmbientM.invariant] at hr
      cases hr
    | some actual =>
      have he : actual = p ∧ w = v ∧ ambient = ambient' := by
        simpa [getPeer, getDev, hd, hp, and_assoc] using hr
      exact ⟨he.2.1.symm, he.2.2.symm, d, rfl, he.1 ▸ hp⟩

/-- Allocation's complete native endpoint, including arbitrary occupied-slot
inputs; no assumed global freshness is needed for material retention. -/
theorem create_some (word : Option PeerId) (w v : WGWorld) (id : KeypairId)
    (ambient ambient' : Ambient)
    (hr : ((keypairCreate word).run w).run ambient = .ok ((some id, v), ambient')) :
    ∃ d, w.dev = some d ∧ id = d.nextKeypairId ∧ v = keyAllocationWorld w d word := by
  rw [keypairCreate_factor, bind_ok_ambient] at hr
  obtain ⟨ok, a, allocAmbient, ha, hr⟩ := hr
  have hk : a = w := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.hiddenAlloc .kzallocKeypair) (fun g => g = w))
    w ambient ok a allocAmbient rfl ha
  subst a
  simp only [branch, StateT.run_monadLift, monadLift_self, StateT.run_bind,
    CounterWindow.branch_run, CounterWindow.except_ok_bind, StateT.run_pure,
    CounterWindow.except_pure] at hr
  cases ok with
  | false => simp at hr
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind] at hr
    rw [keypairCreateCore_run] at hr
    cases hd : w.dev with
    | none => simp [hd] at hr
    | some d =>
      simp only [hd, CounterWindow.except_ok_bind, StateT.run_pure, CounterWindow.except_pure,
        Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hr
      exact ⟨d, rfl, hr.1.1.symm, hr.1.2.symm⟩

theorem create_none (word : Option PeerId) (w v : WGWorld)
    (ambient ambient' : Ambient)
    (hr : ((keypairCreate word).run w).run ambient = .ok ((none, v), ambient')) : v = w := by
  rw [keypairCreate_factor, bind_ok_ambient] at hr
  obtain ⟨ok, a, allocAmbient, ha, hr⟩ := hr
  have hk : a = w := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.hiddenAlloc .kzallocKeypair) (fun g => g = w))
    w ambient ok a allocAmbient rfl ha
  subst a
  simp only [branch, StateT.run_monadLift, monadLift_self, StateT.run_bind,
    CounterWindow.branch_run, CounterWindow.except_ok_bind, StateT.run_pure,
    CounterWindow.except_pure] at hr
  cases ok with
  | false =>
    simp only [Bool.not_false, ↓reduceIte, StateT.run_pure, CounterWindow.except_pure, Except.ok.injEq,
      Prod.mk.injEq, true_and] at hr
    exact hr.1.symm
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind] at hr
    rw [keypairCreateCore_run] at hr
    cases hd : w.dev <;> simp [hd] at hr

/-- Between the initial read and the saved Context peer read, only a fresh
key allocation changes WG state. The complete entry peer record is equal. -/
theorem entered_peer (pid : PeerId) (ctx : SessionOrigin.Context) (w v : WGWorld)
    (ambient ambient' : Ambient) (he : SessionOrigin.Entered pid ctx w v ambient ambient') :
    ∃ d, w.dev = some d ∧ d.peers[pid]? = some ctx.peer ∧
      ctx.state = ctx.peer.handshakeState ∧ ctx.word = ctx.peer.handshakeEntryPeer ∧
      ctx.slot = d.nextKeypairId ∧ v = keyAllocationWorld w d ctx.word := by
  obtain ⟨initial, a, aAmbient, b, bAmbient, c, cAmbient, d, dAmbient, e, eAmbient,
    hp, hs, hrej, hw, hcreate, hbr, hq⟩ := he
  obtain ⟨ha, haAmbient, dev, hd, hresident⟩ := getPeer_return _ _ _ _ _ _ hp
  subst a
  subst aAmbient
  have hb : b = w := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (sessionStateRejected initial.handshakeState) (fun g => g = w))
    w ambient false b bAmbient rfl hrej
  subst b
  have hc : c = w := (hoare_iff_run_ambient _ _ _).mp
    (indexOwner_peerWord_preserves (.handshake pid) (fun g => g = w))
    w bAmbient ctx.word c cAmbient rfl hw
  subst c
  have hword : ctx.word = initial.handshakeEntryPeer := by
    simpa [IndexOwner.peerWord, getPeer, getDev, hd, hresident, Except.map] using
      congrArg (fun o => o.map (fun out => out.1.1)) hw.symm
  obtain ⟨dev', hcdev, hslot, hdk⟩ := create_some _ _ _ _ _ _ hcreate
  have eqdev : dev' = dev := Option.some.inj (hcdev.symm.trans hd)
  subst dev'
  have hek : e = d := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.branch .sessionNoKeypair (Option.isNone (some ctx.slot)))
      (fun g => g = d)) d dAmbient false e eAmbient rfl hbr
  obtain ⟨hv, _, dev', hedev, hresident2⟩ := getPeer_return _ _ _ _ _ _ hq
  subst v
  have heq : dev' = keyAllocationDevice dev (w.keypairCounter + 1) ctx.word := by
    apply Option.some.inj
    simpa [hek, hdk, keyAllocationWorld] using hedev.symm
  subst dev'
  have hpq : ctx.peer = initial := Option.some.inj (hresident2.symm.trans hresident)
  subst initial
  exact ⟨dev, hd, hresident, hs, hword, hslot, hek.trans hdk⟩

/-- The initializer preserves allocation identity and receiving material. -/
theorem initKey_effect (id : KeypairId) (initiator : Bool) (remote : Nat)
    (w v : WGWorld) (ambient ambient' : Ambient)
    (hr : ((SessionOrigin.initKey id initiator remote).run w).run ambient = .ok (((), v), ambient')) :
    ∃ d k, w.dev = some d ∧ d.keypairs[id]? = some k ∧
      v.dev = some {d with keypairs := d.keypairs.insert id {k with iAmTheInitiator := initiator, remoteIndex := remote}} := by
  unfold SessionOrigin.initKey at hr
  rw [bind_ok_ambient] at hr
  obtain ⟨k, u, middle, hg, hs⟩ := hr
  obtain ⟨rfl, rfl, d, hd, hk⟩ := KeyTimes.getKeypair_return _ _ _ _ _ _ hg
  simp only [CounterWindow.setKeypair_run, Except.ok.injEq, Prod.mk.injEq, true_and] at hs
  rw [← hs.1]
  exact ⟨d, k, hd, hk, by simp [CounterWindow.store, hd]⟩

theorem derive_effect (id : KeypairId) (initiator : Bool) (ck : List UInt8)
    (w v : WGWorld) (ambient ambient' : Ambient)
    (hr : ((deriveKeys id initiator ck).run w).run ambient = .ok (((), v), ambient')) :
    ∃ d old key, w.dev = some d ∧ d.keypairs[id]? = some old ∧
      v.dev = some {d with keypairs := d.keypairs.insert id key} ∧
      key.internalId = old.internalId ∧ key.peer = old.peer ∧ key.receiving.isValid = true := by
  obtain ⟨born, a, aAmbient, outs, b, bAmbient, first, c, cAmbient, second, d, dAmbient,
    old, e, eAmbient, ha, hb, hc, hd, hg, rfl, _⟩ :=
    deriveKeys_execution _ _ _ _ _ _ _ hr
  have ka : a = w := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.hiddenClock64 .deriveKeysBirthdate) (fun g => g = w))
    w ambient born a aAmbient rfl ha
  have kb : b = a := (ProjectedAction.iff_run_ambient _ _ _).mp
    (kdf_sameWGWorld true false ck []) a aAmbient outs b bAmbient hb
  have kc : c = b := (ProjectedAction.iff_run_ambient _ _ _).mp
    (kdfOut_sameWGWorld outs 0) b bAmbient first c cAmbient hc
  have kd : d = c := (ProjectedAction.iff_run_ambient _ _ _).mp
    (kdfOut_sameWGWorld outs 1) c cAmbient second d dAmbient hd
  obtain ⟨he, _, dev, hdev, hold⟩ := KeyTimes.getKeypair_return _ _ _ _ _ _ hg
  subst e
  have same : d = w := kd.trans (kc.trans (kb.trans ka))
  let key : Keypair := if initiator then
    {old with sending := {key := first, birthdate := born, isValid := true}, receiving := {key := second, birthdate := born, isValid := true}}
    else {old with receiving := {key := first, birthdate := born, isValid := true}, sending := {key := second, birthdate := born, isValid := true}}
  refine ⟨dev, old, key, by simpa [same] using hdev, hold, ?_, ?_, ?_, ?_⟩
  · simp [CounterWindow.store, hdev, key]
  all_goals dsimp [key]; split <;> rfl

/-- Successful front installation retains the actual entry peer and exact key. -/
theorem front_effect (pid : PeerId) (ctx : SessionOrigin.Context) (w v : WGWorld)
    (ambient ambient' : Ambient)
    (hr : ((SessionOrigin.front pid).run w).run ambient = .ok ((some ctx, v), ambient')) :
    ∃ d key, w.dev = some d ∧ d.peers[pid]? = some ctx.peer ∧
      ctx.state = ctx.peer.handshakeState ∧ ctx.word = ctx.peer.handshakeEntryPeer ∧
      ctx.slot = d.nextKeypairId ∧
      view v = some (d.ifindex, fun q => if ctx.slot = q then some key else d.keypairs[q]?) ∧
      key.internalId = w.keypairCounter + 1 ∧ key.peer = ctx.word ∧ key.receiving.isValid = true := by
  obtain ⟨read, init, derive, readAmbient, initAmbient, deriveAmbient, entered, _, hi, hb, hr, _⟩ :=
    SessionOrigin.front_material _ _ _ _ _ _ hr
  obtain ⟨d, hd, hp, hs, hw, hslot, hread⟩ := entered_peer _ _ _ _ _ _ entered
  obtain ⟨dev, old, hdev, hold, hinit⟩ := initKey_effect _ _ _ _ _ _ _ hi
  have ed : dev = keyAllocationDevice d (w.keypairCounter + 1) ctx.word := by
    apply Option.some.inj
    simpa [hread, keyAllocationWorld] using hdev.symm
  subst dev
  have eold : old = ({internalId := w.keypairCounter + 1, peer := ctx.word} : Keypair) := by
    simpa [keyAllocationDevice, hslot] using hold.symm
  subst old
  have hb : derive = init := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.branch .sessionInitiator
      (ctx.state == HANDSHAKE_CONSUMED_RESPONSE)) (fun g => g = init))
    init initAmbient ctx.initiator derive deriveAmbient rfl hb
  obtain ⟨dev, key, result, hdev, hkey, hresult, hstamp, hword, hvalid⟩ :=
    derive_effect _ _ _ _ _ _ _ hr
  have ed : dev = {keyAllocationDevice d (w.keypairCounter + 1) ctx.word with
      keypairs := (keyAllocationDevice d (w.keypairCounter + 1) ctx.word).keypairs.insert ctx.slot
        {internalId := w.keypairCounter + 1, peer := ctx.word,
         iAmTheInitiator := ctx.state == HANDSHAKE_CONSUMED_RESPONSE, remoteIndex := ctx.peer.remoteIndex}} := by
    exact Option.some.inj (hdev.symm.trans (by simpa [hb] using hinit))
  subst dev
  simp only [Std.TreeMap.getElem?_insert_self, Option.some.injEq] at hkey
  subst key
  refine ⟨d, result, hd, hp, hs, hw, hslot, ?_, hstamp, hword, hvalid⟩
  simp only [view, hresult, Option.map_some]
  apply congrArg some
  apply Prod.ext (by rfl)
  funext q
  by_cases he : ctx.slot = q
  · subst q; simp
  · simp [keyAllocationDevice, ← hslot, Std.TreeMap.getElem?_insert, he]

theorem front_none (pid : PeerId) (w v : WGWorld) (ambient ambient' : Ambient)
    (hr : ((SessionOrigin.front pid).run w).run ambient = .ok ((none, v), ambient')) : v = w := by
  unfold SessionOrigin.front SessionOrigin.frontWith at hr
  rw [bind_ok_ambient] at hr
  obtain ⟨p, a, aAmbient, hp, hr⟩ := hr
  obtain ⟨ha, haAmbient, _, _, _⟩ := getPeer_return _ _ _ _ _ _ hp
  subst a
  subst aAmbient
  rw [bind_ok_ambient] at hr
  obtain ⟨reject, b, bAmbient, hb, hr⟩ := hr
  have kb : b = w := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (sessionStateRejected p.handshakeState) (fun g => g = w))
    w ambient reject b bAmbient rfl hb
  cases reject with
  | true =>
    have hv : v = b := by simpa [Except.map] using congrArg (fun out => out.map (fun x => x.1.2)) hr.symm
    exact hv.trans kb
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, bind_ok_ambient] at hr
    obtain ⟨word, c, cAmbient, hw, created, d, dAmbient, hc, missing, e, eAmbient, hm, hr⟩ := hr
    have kc : c = b := (hoare_iff_run_ambient _ _ _).mp
      (indexOwner_peerWord_preserves (.handshake pid) (fun g => g = b))
      b bAmbient word c cAmbient rfl hw
    have he : missing = created.isNone ∧ e = d ∧
        eAmbient = CounterWindow.record dAmbient .sessionNoKeypair created.isNone := by
      simpa [branch, CounterWindow.branch_run, eq_comm, and_assoc] using hm
    obtain ⟨hemissing, heworld, heambient⟩ := he
    subst missing
    subst e
    subst eAmbient
    cases created with
    | none =>
      have hv : v = d := by
        simpa [Except.map] using congrArg (fun out => out.map (fun x => x.1.2)) hr.symm
      exact hv.trans ((create_none _ _ _ _ _ hc).trans (kc.trans kb))
    | some id =>
      simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte, bind_ok_ambient] at hr
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, he⟩ := hr
      simp at he

/-- Support is emitted at front completion, before the session suffix. -/
theorem front_installs (pid : PeerId) (w v : WGWorld) (result : Option SessionOrigin.Context)
    (ambient ambient' : Ambient) (history : List SessionOrigin.Receipt) (hi : Inv history w)
    (hr : ((SessionOrigin.front pid).run w).run ambient = .ok ((result, v), ambient')) :
    Inv (history ++ [.material pid ⟨result, w, v, ambient, ambient'⟩]) v := by
  cases result with
  | none =>
    have hk := front_none pid w v ambient ambient' hr
    have hv : view v = view w := by rw [hk]
    exact InvView.mono (hv ▸ hi) (fun r h => List.mem_append_left _ h)
  | some ctx =>
    obtain ⟨d, key, hd, hp, hs, hw, hslot, hview, hstamp, hword, hvalid⟩ :=
      front_effect _ _ _ _ _ _ hr
    intro epoch keys hv id k hk valid
    rw [hview] at hv
    cases hv
    by_cases he : ctx.slot = id
    · subst id
      simp only [↓reduceIte, Option.some.injEq] at hk
      subst k
      obtain ⟨dev, hdev⟩ : ∃ dev, v.dev = some dev := by
        cases h : v.dev with
        | none => simp [view, h] at hview
        | some dev => exact ⟨dev, rfl⟩
      have fields : (d.ifindex, fun q => if ctx.slot = q then some key else d.keypairs[q]?) =
          (dev.ifindex, fun q => dev.keypairs[q]?) := by
        simpa [view, hdev] using hview.symm
      have epoch : dev.ifindex = d.ifindex := (congrArg Prod.fst fields).symm
      have keyeq : dev.keypairs[ctx.slot]? = some key := by
        have h := congrFun (congrArg Prod.snd fields) ctx.slot
        simpa using h.symm
      exact ⟨pid, ⟨some ctx, w, v, ambient, ambient'⟩, ctx, dev, key,
        by simp, hr, rfl, rfl, hdev, epoch, keyeq, hvalid, hword, rfl, Or.inr hword⟩
    · have old : d.keypairs[id]? = some k := by simpa [he] using hk
      exact (hi d.ifindex (fun q => d.keypairs[q]?) (by simp [view, hd]) id k old valid).mono
        (fun r h => List.mem_append_left _ h)

def receipt? : MaterialOrigin.Event R → Option R
  | .life _ => none | .receipt r => some r

def SessionInv (h : List (MaterialOrigin.Event SessionOrigin.Receipt)) (w : WGWorld) : Prop :=
  MaterialOrigin.Valid SessionOrigin.Receipt.Valid h ∧ Inv (h.filterMap receipt?) w

/-- Journal focusing is independent of the actual single state carrier. -/
theorem access_receipts {S : Type} (a : PrefixT LifetimeEvent S α) (w : S)
    (h : List (MaterialOrigin.Event R)) :
    (runPrefix (MaterialOrigin.access a) w h).2.filterMap receipt? = h.filterMap receipt? :=
  focusPrefix_other _ _ receipt? (fun _ => rfl) a w h

/-- Preserve the original arbitrary product action instance through a pure view. -/
theorem access_support {S : Type} (project : S → WGWorld)
    (a : PrefixT LifetimeEvent S α) (original : StateT S (Except Stop) α)
    (he : ErasesPrefix a original)
    (retain : ∀ w x v, original.run w = .ok (x, v) → Retains (project w) (project v)) :
    PrefixPreserves (fun h w => SessionInv h (project w))
      (MaterialOrigin.Valid SessionOrigin.Receipt.Valid) (MaterialOrigin.access a) := by
  intro w h hi
  obtain ⟨suffix, hs, hv, _⟩ := access_valid a SessionOrigin.Receipt.Valid w h hi.1
  refine ⟨suffix, hs, hv, ?_⟩
  cases hr : (runPrefix (MaterialOrigin.access a) w h).1 with
  | error e => trivial
  | ok out =>
    refine ⟨hv, ?_⟩
    rw [access_receipts]
    exact hi.2.retain (retain w out.1 out.2 ((access_erases he w h).symm.trans hr))

def accessNative (a : MixedM α) : WGPrefix (MaterialOrigin.Event R) α :=
  focusStatePrefix MaterialOrigin.Event.life MaterialOrigin.life? a

theorem access_support_native (a : MixedM α) (original : WG.M α)
    (he : ErasesStatePrefix a original)
    (retain : ∀ w ambient x v ambient',
      (original.run w).run ambient = .ok ((x, v), ambient') → Retains w v) :
    StatePrefixPreserves (fun h w _ => SessionInv h w)
      (MaterialOrigin.Valid SessionOrigin.Receipt.Valid) (accessNative a) := by
  intro w ambient h hi
  obtain ⟨suffix, hs, hv, _⟩ :=
    access_valid (a.run w) SessionOrigin.Receipt.Valid ambient h hi.1
  refine ⟨suffix, hs, hv, ?_⟩
  cases hr : (runPrefix ((accessNative a).run w) ambient h).1 with
  | error e => trivial
  | ok out =>
    rcases out with ⟨⟨x, v⟩, ambient'⟩
    refine ⟨hv, ?_⟩
    change Inv ((runWGPrefix (accessNative a) w ambient h).2.filterMap receipt?) v
    rw [show (runWGPrefix (accessNative a) w ambient h).2.filterMap receipt? =
      h.filterMap receipt? from access_receipts (a.run w) ambient h]
    exact hi.2.retain (retain w ambient x v ambient'
      ((focusStatePrefix_erases _ _ he w ambient h).symm.trans hr))

theorem front_observer_support (pid : PeerId) :
    StatePrefixEnsures (fun h w _ => SessionInv h w)
      (MaterialOrigin.Valid SessionOrigin.Receipt.Valid)
      (receiptWGObserved (SessionOrigin.observedFront pid)
        (MaterialOrigin.Event.receipt ∘ SessionOrigin.Receipt.material pid))
      (fun _ h w _ => SessionInv h w) := by
  intro w ambient h hi
  obtain ⟨s, hs, hv, _⟩ := SessionOrigin.observedFront_valid pid w ambient h hi.1
  have hc := runWGPrefix_receiptWGObserved (SessionOrigin.observedFront pid)
    (MaterialOrigin.Event.receipt ∘ SessionOrigin.Receipt.material pid) w ambient h
  simp only [runWGPrefix, runStatePrefix] at hc
  rw [hc]
  cases hr : runPrefix ((SessionOrigin.observedFront pid).run w) ambient h with
  | mk result t =>
    simp only [hr] at hs hv
    cases result with
    | error e => exact ⟨s, hs, hv, trivial⟩
    | ok out =>
      rcases out with ⟨⟨result, v⟩, ambient'⟩
      have run : ((SessionOrigin.front pid).run w).run ambient = .ok ((result, v), ambient') :=
        (SessionOrigin.observedFront_erases pid w ambient h).symm.trans (congrArg Prod.fst hr)
      have truth : MaterialOrigin.Valid SessionOrigin.Receipt.Valid
          (t ++ [.receipt (.material pid ⟨result, w, v, ambient, ambient'⟩)]) := by
        intro e he
        rcases List.mem_append.mp he with he | he
        · exact hv e he
        · simp only [List.mem_singleton] at he
          subst e
          exact run
      have supported := front_installs pid w v result ambient ambient'
        (h.filterMap receipt?) hi.2 run
      refine ⟨s ++ [.receipt (.material pid ⟨result, w, v, ambient, ambient'⟩)],
        by simp [hs, List.append_assoc], truth, truth, ?_⟩
      apply supported.mono
      intro r hm
      simp only [List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | rfl
      · rw [hs]
        simp only [List.filterMap_append, List.mem_append]
        exact Or.inl (Or.inl hm)
      · simp [receipt?]

theorem session_support (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => SessionInv h w)
      (MaterialOrigin.Valid SessionOrigin.Receipt.Valid) (SessionOrigin.observed pid) := by
  unfold SessionOrigin.observed
  apply StatePrefixEnsures.bind (front_observer_support pid)
  intro result
  cases result with
  | none => exact StatePrefixEnsures.pure false (fun _ _ _ hi => hi.1) (fun _ _ _ hi => hi)
  | some ctx =>
    exact access_support_native (SessionOrigin.tailPrefix pid ctx.slot) (SessionOrigin.tail pid ctx.slot)
      (SessionOrigin.tail_erases _ _) (fun _ ambient _ _ ambient' hr => tail_retains pid ctx.slot ambient ambient' hr)

theorem decrypt_supported (history : List SessionOrigin.Receipt) (id : SkbId)
    (r : WGRunWitness (RxPacket × Option RxPacket)) (out : RxPacket)
    (hi : Inv history r.before) (hr : r.Valid (RxOrigin.readDecrypt id)) (ho : r.value.2 = some out) :
    ∃ d k, r.before.dev = some d ∧ d.rxSkbs[id]? = some r.value.1 ∧
      d.keypairs[r.value.1.keypair]? = some k ∧ Supported history d.ifindex r.value.1.keypair k ∧
      ((decryptPacket r.value.1).run r.before).run r.ambientBefore = .ok ((some out, r.after), r.ambientAfter) ∧
      out = {r.value.1 with nonce := u64le r.value.1.bytes 8, bytes := out.bytes} ∧
      aeadDecrypt k.receiving.key (counterNonce (u64le r.value.1.bytes 8))
        (r.value.1.bytes.drop 16) [] = some out.bytes := by
  obtain ⟨d,k,hd,hp,hk,hv,hr,ho,ha⟩ := RxOrigin.decrypt_receipt id r out hr ho
  exact ⟨d,k,hd,hp,hk,hi d.ifindex (fun q => d.keypairs[q]?) (by simp [view,hd]) _ k hk hv,hr,ho,ha⟩

inductive Event where
  | life : LifetimeEvent → Event
  | session : SessionOrigin.Receipt → Event
  | rx : RxOrigin.Receipt → Event

def sessionEncode : MaterialOrigin.Event SessionOrigin.Receipt → Event
  | .life e => .life e | .receipt r => .session r

def sessionDecode : Event → Option (MaterialOrigin.Event SessionOrigin.Receipt)
  | .life e => some (.life e) | .session r => some (.receipt r) | .rx _ => none

def rxEncode : MaterialOrigin.Event RxOrigin.Receipt → Event
  | .life e => .life e | .receipt r => .rx r

def rxDecode : Event → Option (MaterialOrigin.Event RxOrigin.Receipt)
  | .life e => some (.life e) | .session _ => none | .rx r => some (.receipt r)

def lifetime : Event → Option LifetimeEvent
  | .life e => some e | _ => none

def sessionReceipt : Event → Option SessionOrigin.Receipt
  | .session r => some r | _ => none

def sessions (h : List Event) := h.filterMap sessionReceipt

def localSession (pid : PeerId) : WGPrefix Event Bool :=
  focusStatePrefix sessionEncode sessionDecode (SessionOrigin.observed pid)

def localDecrypt (id : SkbId) : WGPrefix Event (RxPacket × Option RxPacket) :=
  focusStatePrefix rxEncode rxDecode (RxOrigin.decrypt id)

theorem localSession_erases (pid : PeerId) : ErasesStatePrefix (localSession pid) (beginSession pid) :=
  focusStatePrefix_erases _ _ (SessionOrigin.observed_erases pid)

theorem localDecrypt_erases (id : SkbId) : ErasesStatePrefix (localDecrypt id) (RxOrigin.readDecrypt id) :=
  focusStatePrefix_erases _ _ (RxOrigin.decrypt_erases id)

theorem session_filter (h : List Event) :
    (h.filterMap sessionDecode).filterMap receipt? = sessions h := by
  induction h with
  | nil => rfl
  | cons e h ih => cases e <;> simp [sessionDecode,receipt?,sessions,sessionReceipt] at * <;> exact ih

theorem localSession_support (pid : PeerId) :
    StatePrefixPreserves
      (fun h w _ => MaterialOrigin.Valid SessionOrigin.Receipt.Valid (h.filterMap sessionDecode) ∧ Inv (sessions h) w)
      (fun h => MaterialOrigin.Valid SessionOrigin.Receipt.Valid (h.filterMap sessionDecode))
      (localSession pid) := by
  have h := StatePrefixEnsures.focus sessionEncode sessionDecode (by intro e; cases e <;> rfl)
    (session_support pid)
  simpa only [SessionInv, session_filter, localSession] using h

theorem sessionSource_appends (pid : PeerId) : StateAppends (SessionOrigin.observed pid) := by
  unfold SessionOrigin.observed SessionOrigin.observedFront SessionOrigin.frontWith
  simp only [SessionOrigin.allocate]
  repeat' first
    | with_reducible exact StateAppends.focus _ _ _
    | with_reducible exact StateAppends.lift _
    | with_reducible exact StateAppends.pure _
    | with_reducible apply StateAppends.receiptWGObserved
    | with_reducible apply StateAppends.bind
    | (session_origin_intro_forall; try dsimp only)
    | split
  all_goals first | exact StateAppends.focus _ _ _ | exact StateAppends.lift _

/-- The local adapter retains the exact incoming lifetime history and all
failed-prefix accesses. No material-support premise is added to R2 projection. -/
theorem adapter_projects {S : Type} {I : List LifetimeEvent → S → Prop}
    (encode : MaterialOrigin.Event R → Event)
    (decode : Event → Option (MaterialOrigin.Event R))
    (hin : ∀ e, (decode e).bind MaterialOrigin.life? = lifetime e)
    (hout : ∀ e, lifetime (encode e) = MaterialOrigin.life? e)
    (g : PrefixT (MaterialOrigin.Event R) S α) (a : PrefixT LifetimeEvent S α)
    (ha : Appends g) (hp : ProjectsUnder I MaterialOrigin.life? g a) :
    ProjectsUnder I lifetime (focusPrefix encode decode g) a := by
  intro w h hi
  have input : (h.filterMap decode).filterMap MaterialOrigin.life? = h.filterMap lifetime := by
    simp only [List.filterMap_filterMap]
    congr 1
    funext e
    exact hin e
  have projected := hp w (h.filterMap decode) (by simpa [input] using hi)
  obtain ⟨s, hs⟩ := ha w (h.filterMap decode)
  have equation : runPrefix g w (h.filterMap decode) =
      ((runPrefix g w (h.filterMap decode)).1, h.filterMap decode ++ s) := Prod.ext rfl hs
  rw [focusPrefix_suffix encode decode g w h _ s equation]
  have output : (s.map encode).filterMap lifetime = s.filterMap MaterialOrigin.life? := by
    simp only [List.filterMap_map]
    congr 1
    funext e
    exact hout e
  simpa only [hs, input, List.filterMap_append, output] using projected

theorem localSession_projects (pid : PeerId) :
    StateProjectsUnder (fun h w _ => AllocationInv h w) lifetime
      (localSession pid) (beginSessionPrefix pid) := by
  intro w
  exact adapter_projects (I := fun h (_ : Ambient) => AllocationInv h w)
    sessionEncode sessionDecode (by intro e; cases e <;> rfl) (by intro e; cases e <;> rfl)
    ((SessionOrigin.observed pid).run w) ((beginSessionPrefix pid).run w)
    (sessionSource_appends pid w) (SessionOrigin.observed_projects pid w)

theorem localDecrypt_projects (id : SkbId) :
    StateProjectsUnder (fun h w _ => AllocationInv h w) lifetime
      (localDecrypt id) (RxOrigin.readDecryptPrefix id) := by
  intro w
  have ha : StateAppends (RxOrigin.decrypt id) :=
    (StateAppends.focus _ _ _).receiptWGObserved _
  exact adapter_projects (I := fun h (_ : Ambient) => AllocationInv h w)
    rxEncode rxDecode (by intro e; cases e <;> rfl) (by intro e; cases e <;> rfl)
    ((RxOrigin.decrypt id).run w) ((RxOrigin.readDecryptPrefix id).run w)
    (ha w) (RxOrigin.decrypt_projects id w)

theorem rx_lifetime (h : List Event) :
    (h.filterMap rxDecode).filterMap MaterialOrigin.life? = h.filterMap lifetime := by
  simp only [List.filterMap_filterMap]
  congr 1
  funext e
  cases e <;> rfl

/-- Exact local execution equation. The original RX observer executes once at
its actual projected incoming lifetime history. Stop emits no successful run. -/
theorem localDecrypt_run (id : SkbId) (w : WGWorld) (ambient : Ambient) (h : List Event) :
    let out := runWGPrefix (RxOrigin.readDecryptPrefix id) w ambient (h.filterMap lifetime)
    let suffix := (out.2.drop (h.filterMap lifetime).length).map Event.life
    runWGPrefix (localDecrypt id) w ambient h = match out.1 with
      | .error e => (.error e,h ++ suffix)
      | .ok ((result, v), ambient') => (.ok ((result, v), ambient'), h ++ suffix ++ [.rx (.decrypt id ⟨result, w, v, ambient, ambient'⟩)]) := by
  have ha : runWGPrefix (accessNative (RxOrigin.readDecryptPrefix id)) w ambient (h.filterMap rxDecode) =
      ((runWGPrefix (RxOrigin.readDecryptPrefix id) w ambient (h.filterMap lifetime)).1,
        h.filterMap rxDecode ++
          ((runWGPrefix (RxOrigin.readDecryptPrefix id) w ambient (h.filterMap lifetime)).2.drop
            (h.filterMap lifetime).length).map MaterialOrigin.Event.life) := by
    change ((runWGPrefix (RxOrigin.readDecryptPrefix id) w ambient ((h.filterMap rxDecode).filterMap MaterialOrigin.life?)).1,
      h.filterMap rxDecode ++
        ((runWGPrefix (RxOrigin.readDecryptPrefix id) w ambient ((h.filterMap rxDecode).filterMap MaterialOrigin.life?)).2.drop
          ((h.filterMap rxDecode).filterMap MaterialOrigin.life?).length).map MaterialOrigin.Event.life) = _
    rw [rx_lifetime]
  dsimp only
  unfold localDecrypt
  change ((runWGPrefix (RxOrigin.decrypt id) w ambient (h.filterMap rxDecode)).1,
    h ++ ((runWGPrefix (RxOrigin.decrypt id) w ambient (h.filterMap rxDecode)).2.drop (h.filterMap rxDecode).length).map rxEncode) = _
  unfold RxOrigin.decrypt
  change ((runWGPrefix (receiptWGObserved (accessNative (RxOrigin.readDecryptPrefix id))
    (MaterialOrigin.Event.receipt ∘ RxOrigin.Receipt.decrypt id)) w ambient (h.filterMap rxDecode)).1,
    h ++ ((runWGPrefix (receiptWGObserved (accessNative (RxOrigin.readDecryptPrefix id))
    (MaterialOrigin.Event.receipt ∘ RxOrigin.Receipt.decrypt id)) w ambient (h.filterMap rxDecode)).2.drop
      (h.filterMap rxDecode).length).map rxEncode) = _
  rw [runWGPrefix_receiptWGObserved, ha]
  cases hr : runWGPrefix (RxOrigin.readDecryptPrefix id) w ambient (h.filterMap lifetime) with
  | mk result t =>
    cases result with
    | error e => simp [List.map_map,Function.comp_def,rxEncode]
    | ok out =>
      rcases out with ⟨⟨result, v⟩, ambient'⟩
      simp [List.map_map,Function.comp_def,rxEncode,List.append_assoc]

/-- A successful new decrypt receipt follows its material witness strictly in
this same local journal. The incoming support premise is explicit: arbitrary
input receipts need not be reached occurrences of an initialized Runner. -/
theorem localDecrypt_origin (id : SkbId) (w : WGWorld) (ambient : Ambient) (h : List Event)
    (packet out : RxPacket) (v : WGWorld) (ambient' : Ambient)
    (hi : Inv (sessions h) w)
    (hr : (runWGPrefix (localDecrypt id) w ambient h).1 = .ok (((packet, some out), v), ambient')) :
    ∃ (suffix : List LifetimeEvent) (d : Device) (k : Keypair) (pid : PeerId)
      (r : WGRunWitness (Option SessionOrigin.Context)) (ctx : SessionOrigin.Context)
      (originDev : Device) (original : Keypair) (before middle : List Event),
      (runWGPrefix (localDecrypt id) w ambient h).2 =
        h ++ suffix.map Event.life ++ [.rx (.decrypt id ⟨(packet, some out), w, v, ambient, ambient'⟩)] ∧
      h = before ++ [.session (.material pid r)] ++ middle ∧
      r.Valid (SessionOrigin.front pid) ∧ r.value = some ctx ∧ ctx.slot = packet.keypair ∧
      r.after.dev = some originDev ∧ originDev.ifindex = d.ifindex ∧
      originDev.keypairs[packet.keypair]? = some original ∧ original.receiving.isValid = true ∧
      original.peer = ctx.word ∧ material k = material original ∧ WordLe k.peer ctx.word ∧
      w.dev = some d ∧ d.rxSkbs[id]? = some packet ∧ d.keypairs[packet.keypair]? = some k ∧
      ((decryptPacket packet).run w).run ambient = .ok ((some out, v), ambient') ∧
      out = {packet with nonce := u64le packet.bytes 8, bytes := out.bytes} ∧
      aeadDecrypt k.receiving.key (counterNonce (u64le packet.bytes 8)) (packet.bytes.drop 16) [] = some out.bytes := by
  have original : ((RxOrigin.readDecrypt id).run w).run ambient = .ok (((packet, some out), v), ambient') :=
    (localDecrypt_erases id w ambient h).symm.trans hr
  obtain ⟨d,k,hd,hp,hk,support,hdc,record,aead⟩ :=
    decrypt_supported (sessions h) id ⟨(packet, some out), w, v, ambient, ambient'⟩ out hi original rfl
  obtain ⟨pid,r,ctx,originDev,old,mem,hv,hctx,hslot,ho,he,hkey,hvalid,hword,hmat,keep⟩ := support
  obtain ⟨event,hm,hevent⟩ := List.mem_filterMap.mp mem
  have eventEq : event = .session (.material pid r) := by
    cases event <;> simp only [sessionReceipt,Option.some.injEq,reduceCtorEq] at hevent
    subst hevent
    rfl
  subst event
  obtain ⟨before,middle,hist⟩ := List.mem_iff_append.mp hm
  have observed : (runWGPrefix (RxOrigin.readDecryptPrefix id) w ambient (h.filterMap lifetime)).1 =
      .ok (((packet, some out), v), ambient') := (RxOrigin.readDecrypt_erases id w ambient _).trans original
  refine ⟨(runWGPrefix (RxOrigin.readDecryptPrefix id) w ambient (h.filterMap lifetime)).2.drop (h.filterMap lifetime).length,d,k,pid,r,ctx,originDev,old,before,middle,?_,?_,hv,hctx,hslot,ho,he,hkey,hvalid,hword,hmat,keep,hd,hp,hk,hdc,record,aead⟩
  · rw [localDecrypt_run,observed]
  · simpa [List.append_assoc] using hist

theorem create_retains (word : Option PeerId) (w v : WGWorld) (result : Option KeypairId)
    (ambient ambient' : Ambient)
    (hr : ((keypairCreate word).run w).run ambient = .ok ((result, v), ambient')) : Retains w v := by
  cases result with
  | none =>
    have hk := create_none word w v ambient ambient' hr
    rw [hk]
    exact Retains.refl _
  | some id =>
    obtain ⟨d, hd, hid, hv⟩ := create_some word w v id ambient ambient' hr
    have retain := retains_insert d.ifindex (fun q => d.keypairs[q]?) d.nextKeypairId
      ({internalId := w.keypairCounter + 1, peer := word} : Keypair) (by intro bad; cases bad)
    simpa [Retains, view, hv, keyAllocationWorld, keyAllocationDevice, hd,
      Std.TreeMap.getElem?_insert, Std.LawfulEqOrd.compare_eq_iff_eq] using retain

theorem receiveReject_sameWGWorld (k : Keypair) :
    SameView (id : WGWorld → WGWorld) (KeyTimes.receiveReject k) := by
  apply SameView.of_wp
  intro original
  have ht := (branchExpired_sameWGWorld .decKeyExpired k.receiving.birthdate REJECT_AFTER_TIME).wp
    (fun s => s = original)
  mvcgen [KeyTimes.receiveReject, WG.orM, branch, branchCmp, ht, AmbientM.branch, AmbientM.branchCmp]

theorem receiveTail_sameWGWorld (pkt : RxPacket) (k : Keypair) :
    SameView (id : WGWorld → WGWorld) (KeyTimes.receiveTail pkt k) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hr
  simp only [KeyTimes.receiveTail, bind_ok_ambient] at hr
  obtain ⟨ok, entered, middle, ha, hr⟩ := hr
  have hw : entered = w := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.hiddenAlloc .skbCowDataRx) (fun g => g = w))
    w ambient ok entered middle rfl ha
  subst entered
  simp only [WG.orM, branch, StateT.run_monadLift, monadLift_self, StateT.run_bind,
    CounterWindow.branch_run, CounterWindow.except_ok_bind, StateT.run_pure,
    CounterWindow.except_pure] at hr
  cases ok <;>
    cases hp : aeadDecrypt k.receiving.key (counterNonce (u64le pkt.bytes 8))
      (pkt.bytes.drop 16) [] <;> simp_all
  all_goals obtain ⟨u, _, ⟨hu, _⟩, ⟨_, hv⟩, _⟩ := hr
  all_goals exact hv.symm.trans hu.symm

theorem decrypt_spec (P : View → Prop) (stable : Stable P) (pkt : RxPacket) :
    ⦃fun w => ⌜P (view w)⌝⦄ decryptPacket pkt ⦃⇓? _ w => ⌜P (view w)⌝⦄ := by
  rw [KeyTimes.decryptPacket_factor]
  have hg := getKeypair_spec P
  have hs := setKeypair_spec P stable
  have hr := fun k => ((receiveReject_sameWGWorld k).factor view).wp P
  have ht := fun k => ((receiveTail_sameWGWorld pkt k).factor view).wp P
  mvcgen [hg, hs, hr, ht, branch, AmbientM.branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [view]

theorem readDecrypt_retains (id : SkbId) (w v : WGWorld) (result : RxPacket × Option RxPacket)
    (ambient ambient' : Ambient)
    (hr : ((RxOrigin.readDecrypt id).run w).run ambient = .ok ((result, v), ambient')) : Retains w v := by
  have hg : SameView view (getRxSkb id) := by
    intro initial
    apply hoare_liftSkb
    intro g d store hi hdev
    simpa [view, hdev] using hi
  have hs : ⦃fun u => ⌜RetainsView (view w) (view u)⌝⦄ RxOrigin.readDecrypt id
      ⦃⇓? _ u => ⌜RetainsView (view w) (view u)⌝⦄ := by
    have hp := hg.wp (RetainsView (view w))
    have hd := decrypt_spec (RetainsView (view w)) (fun _ _ a b => b.trans a)
    mvcgen [RxOrigin.readDecrypt, hp, hd]
  exact (hoare_iff_run_ambient _ _ _).mp hs w ambient result v ambient' (RetainsView.refl _) hr

theorem localDecrypt_support (id : SkbId) :
    StatePrefixPreserves (fun h w _ => Inv (sessions h) w) (fun _ => True) (localDecrypt id) := by
  intro w ambient h hi
  obtain ⟨suffix, hs⟩ := StateAppends.focus rxEncode rxDecode (RxOrigin.decrypt id) w ambient h
  refine ⟨suffix, hs, trivial, ?_⟩
  cases hr : (runPrefix ((localDecrypt id).run w) ambient h).1 with
  | error e => trivial
  | ok out =>
    rcases out with ⟨⟨result, v⟩, ambient'⟩
    have history : sessions (runWGPrefix (localDecrypt id) w ambient h).2 = sessions h :=
      focusPrefix_other rxEncode rxDecode sessionReceipt (by intro e; cases e <;> rfl)
        ((RxOrigin.decrypt id).run w) ambient h
    change Inv (sessions (runWGPrefix (localDecrypt id) w ambient h).2) v
    rw [history]
    exact hi.retain (readDecrypt_retains id w v result ambient ambient'
      ((localDecrypt_erases id w ambient h).symm.trans hr))

/-- Truth of supplied and newly emitted receipts, independent of R2's access
invariant. Life events are accounted for by the separate exact R2 projection. -/
def Event.Valid : Event → Prop
  | .life _ => True
  | .session r => SessionOrigin.Receipt.Valid r
  | .rx r => RxOrigin.Receipt.Valid r

def Valid (h : List Event) : Prop := ∀ e ∈ h, e.Valid

theorem focus_valid {S : Type} (encode : E → Event) (decode : Event → Option E)
    (valid : E → Prop) (g : PrefixT E S α)
    (hin : ∀ e x, e.Valid → decode e = some x → valid x)
    (hout : ∀ e, valid e → (encode e).Valid)
    (hp : PrefixPreserves (fun h _ => ∀ e ∈ h, valid e) (fun h => ∀ e ∈ h, valid e) g) :
    PrefixPreserves (fun h _ => Valid h) Valid (focusPrefix encode decode g) := by
  intro w h hi
  have input : ∀ e ∈ h.filterMap decode, valid e := by
    intro x hx
    obtain ⟨e,he,hd⟩ := List.mem_filterMap.mp hx
    exact hin e x (hi e he) hd
  obtain ⟨suffix,hs,hv,_⟩ := hp w (h.filterMap decode) input
  have run : runPrefix g w (h.filterMap decode) =
      ((runPrefix g w (h.filterMap decode)).1,h.filterMap decode ++ suffix) := Prod.ext rfl hs
  rw [focusPrefix_suffix encode decode g w h _ suffix run]
  have truth : Valid (h ++ suffix.map encode) := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact hi e he
    · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp he
      apply hout x
      apply hv x
      rw [hs]
      exact List.mem_append_right _ hx
  refine ⟨suffix.map encode,rfl,truth,?_⟩
  cases (runPrefix g w (h.filterMap decode)).1 with
  | error e => trivial
  | ok out => exact truth

theorem localSession_valid (pid : PeerId) :
    StatePrefixPreserves (fun h _ _ => Valid h) Valid (localSession pid) := by
  intro w
  apply focus_valid sessionEncode sessionDecode
    (fun e => match e with | .life _ => True | .receipt r => SessionOrigin.Receipt.Valid r)
    ((SessionOrigin.observed pid).run w)
  · intro e x hv hx
    cases e <;> simp only [sessionDecode, Option.some.injEq, reduceCtorEq] at hx
    all_goals subst x; exact hv
  · intro e hv; cases e <;> exact hv
  · intro ambient h hi
    have input : MaterialOrigin.Valid SessionOrigin.Receipt.Valid h := by
      intro e he; cases e <;> exact hi _ he
    obtain ⟨suffix, hs, hv, _⟩ := SessionOrigin.observed_valid pid w ambient h input
    have truth : ∀ e ∈ (runWGPrefix (SessionOrigin.observed pid) w ambient h).2,
        (match e with | .life _ => True | .receipt r => SessionOrigin.Receipt.Valid r) := by
      intro e he; cases e <;> exact hv _ he
    refine ⟨suffix, hs, truth, ?_⟩
    cases (runPrefix ((SessionOrigin.observed pid).run w) ambient h).1 <;> first | trivial | exact truth

theorem localDecrypt_valid (id : SkbId) :
    StatePrefixPreserves (fun h _ _ => Valid h) Valid (localDecrypt id) := by
  intro w
  apply focus_valid rxEncode rxDecode
    (fun e => match e with | .life _ => True | .receipt r => RxOrigin.Receipt.Valid r)
    ((RxOrigin.decrypt id).run w)
  · intro e x hv hx
    cases e <;> simp only [rxDecode, Option.some.injEq, reduceCtorEq] at hx
    all_goals subst x; exact hv
  · intro e hv; cases e <;> exact hv
  · intro ambient h hi
    have input : MaterialOrigin.Valid RxOrigin.Receipt.Valid h := by
      intro e he; cases e <;> exact hi _ he
    obtain ⟨suffix, hs, hv, _⟩ := RxOrigin.decrypt_valid id w ambient h input
    have truth : ∀ e ∈ (runWGPrefix (RxOrigin.decrypt id) w ambient h).2,
        (match e with | .life _ => True | .receipt r => RxOrigin.Receipt.Valid r) := by
      intro e he; cases e <;> exact hv _ he
    refine ⟨suffix, hs, truth, ?_⟩
    cases (runPrefix ((RxOrigin.decrypt id).run w) ambient h).1 <;> first | trivial | exact truth

end Leanux.Proofs.WG.Origins
