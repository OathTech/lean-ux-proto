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

theorem getPeer_return (pid : PeerId) (w v : World) (p : Peer)
    (hr : (getPeer pid).run w = .ok (p,v)) :
    v = w ∧ ∃ d, w.k.wg = some d ∧ d.peers[pid]? = some p := by
  cases hd : w.k.wg with
  | none => simp [getPeer, getDev, getK, hd, invariant] at hr
  | some d =>
    cases hp : d.peers[pid]? with
    | none => simp [getPeer, getDev, getK, hd, hp, invariant] at hr
    | some actual =>
      have he : actual = p ∧ w = v := by simpa [getPeer, getDev, getK, hd, hp] using hr
      exact ⟨he.2.symm, d, rfl, he.1 ▸ hp⟩

/-- Allocation's complete kernel endpoint, including arbitrary occupied-slot
inputs; no assumed global freshness is needed for material retention. -/
theorem create_some (word : Option PeerId) (w v : World) (id : KeypairId)
    (hr : (keypairCreate word).run w = .ok (some id,v)) :
    ∃ d, w.k.wg = some d ∧ id = d.nextKeypairId ∧
      v.k = (keyAllocationWorld w d word).k := by
  rw [keypairCreate_factor] at hr
  rw [bind_ok] at hr
  obtain ⟨ok,a,ha,hr⟩ := hr
  have hk := hiddenAlloc_sameKernel .kzallocKeypair w ok a ha
  simp only [StateT.run_bind, CounterWindow.branch_run, CounterWindow.except_ok_bind] at hr
  cases ok with
  | false => simp at hr
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hr
    change ((keypairCreateCore word).run (CounterWindow.record a .keypairCreateNoMem false) >>=
      fun out => Except.ok (some out.1,out.2)) = .ok (_,v) at hr
    rw [keypairCreateCore_run] at hr
    cases hd : w.k.wg with
    | none => simp [CounterWindow.record, hk, hd] at hr
    | some d =>
      simp [CounterWindow.record, hk, hd, keyAllocationWorld] at hr
      exact ⟨d,rfl,hr.1.symm,by rw [←hr.2]; rfl⟩

theorem create_none (word : Option PeerId) (w v : World)
    (hr : (keypairCreate word).run w = .ok (none,v)) : v.k = w.k := by
  rw [keypairCreate_factor] at hr
  rw [bind_ok] at hr
  obtain ⟨ok,a,ha,hr⟩ := hr
  have hk := hiddenAlloc_sameKernel .kzallocKeypair w ok a ha
  simp only [StateT.run_bind, CounterWindow.branch_run, CounterWindow.except_ok_bind] at hr
  cases ok with
  | false => simp [CounterWindow.record] at hr; subst v; exact hk
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hr
    change ((keypairCreateCore word).run (CounterWindow.record a .keypairCreateNoMem false) >>=
      fun out => Except.ok (some out.1,out.2)) = .ok (_,v) at hr
    rw [keypairCreateCore_run] at hr
    cases hd : a.k.wg <;> simp [CounterWindow.record, hd] at hr

/-- Between the initial read and the saved Context peer read, only a fresh
key allocation changes the kernel. The complete entry peer record is equal. -/
theorem entered_peer (pid : PeerId) (ctx : SessionOrigin.Context) (w v : World)
    (he : SessionOrigin.Entered pid ctx w v) :
    ∃ d, w.k.wg = some d ∧ d.peers[pid]? = some ctx.peer ∧
      ctx.state = ctx.peer.handshakeState ∧ ctx.word = ctx.peer.handshakeEntryPeer ∧
      ctx.slot = d.nextKeypairId ∧
      v.k = (keyAllocationWorld w d ctx.word).k := by
  obtain ⟨initial,a,b,c,d,e,hp,hs,hrej,hw,hcreate,hbr,hq⟩ := he
  obtain ⟨ha,dev,hd,hresident⟩ := getPeer_return _ _ _ _ hp
  subst a
  have hb := sessionStateRejected_sameKernel _ w false b hrej
  have hc := indexOwner_peerWord_sameKernel (.handshake pid) b ctx.word c hw
  have hword : ctx.word = initial.handshakeEntryPeer := by
    simpa [IndexOwner.peerWord, getPeer, getDev, getK, hb, hd, hresident, Except.map] using
      congrArg (fun o => o.map Prod.fst) hw.symm
  obtain ⟨dev',hcdev,hslot,hdk⟩ := create_some _ _ _ _ hcreate
  have eqdev : dev' = dev := Option.some.inj (hcdev.symm.trans (by simp [hc,hb,hd]))
  subst dev'
  have hek := sameKernel_branch _ _ d false e hbr
  obtain ⟨hv,dev',hedev,hresident2⟩ := getPeer_return _ _ _ _ hq
  subst v
  have heq : dev' = keyAllocationDevice dev (w.k.keypairCounter+1) ctx.word := by
    apply Option.some.inj
    simpa [hek,hdk,keyAllocationWorld,hc,hb] using hedev.symm
  subst dev'
  have hpq : ctx.peer = initial := Option.some.inj (hresident2.symm.trans hresident)
  subst initial
  exact ⟨dev,hd,hresident,hs,hword,hslot,by simpa [hek,hdk,keyAllocationWorld,hc,hb]⟩

/-- The initializer is a concrete record update, preserving allocation identity
and receiving material; no arbitrary setter rule is used. -/
theorem initKey_effect (id : KeypairId) (initiator : Bool) (remote : Nat)
    (w v : World) (hr : (SessionOrigin.initKey id initiator remote).run w = .ok ((),v)) :
    ∃ d k, w.k.wg = some d ∧ d.keypairs[id]? = some k ∧
      v.k.wg = some {d with keypairs := d.keypairs.insert id {k with iAmTheInitiator := initiator, remoteIndex := remote}} := by
  unfold SessionOrigin.initKey at hr
  rw [bind_ok] at hr
  obtain ⟨k,u,hg,hs⟩ := hr
  obtain ⟨rfl,d,hd,hk⟩ := KeyTimes.getKeypair_return _ _ _ _ hg
  simp only [CounterWindow.setKeypair_run, Except.ok.injEq, Prod.mk.injEq, true_and] at hs
  subst v
  exact ⟨d,k,hd,hk,by simp [CounterWindow.store,hd]⟩

theorem derive_effect (id : KeypairId) (initiator : Bool) (ck : List UInt8)
    (w v : World) (hr : (deriveKeys id initiator ck).run w = .ok ((),v)) :
    ∃ d old key, w.k.wg = some d ∧ d.keypairs[id]? = some old ∧
      v.k.wg = some {d with keypairs := d.keypairs.insert id key} ∧
      key.internalId = old.internalId ∧ key.peer = old.peer ∧ key.receiving.isValid = true := by
  obtain ⟨born,a,outs,b,first,c,second,d,old,e,ha,hb,hc,hd,hg,rfl⟩ :=
    deriveKeys_execution _ _ _ _ _ hr
  have ka := hiddenClock64_sameKernel .deriveKeysBirthdate w born a ha
  have kb := kdf_sameKernel true false ck [] a outs b hb
  have kc := kdfOut_sameKernel outs 0 b first c hc
  have kd := kdfOut_sameKernel outs 1 c second d hd
  obtain ⟨he,dev,hdev,hold⟩ := KeyTimes.getKeypair_return _ _ _ _ hg
  subst e
  have same : d.k = w.k := kd.trans (kc.trans (kb.trans ka))
  let key : Keypair := if initiator then
    {old with sending := {key := first, birthdate := born, isValid := true}, receiving := {key := second, birthdate := born, isValid := true}}
    else {old with receiving := {key := first, birthdate := born, isValid := true}, sending := {key := second, birthdate := born, isValid := true}}
  refine ⟨dev,old,key,by simpa [same] using hdev,hold,?_,?_,?_,?_⟩
  · simp [CounterWindow.store,hdev,key]
  all_goals dsimp [key]; split <;> rfl

/-- Successful front installation is tied to the original entry peer and the
exact returned key record. It does not assert that rotation later retains it. -/
theorem front_effect (pid : PeerId) (ctx : SessionOrigin.Context) (w v : World)
    (hr : (SessionOrigin.front pid).run w = .ok (some ctx,v)) :
    ∃ d key, w.k.wg = some d ∧ d.peers[pid]? = some ctx.peer ∧
      ctx.state = ctx.peer.handshakeState ∧ ctx.word = ctx.peer.handshakeEntryPeer ∧
      ctx.slot = d.nextKeypairId ∧
      view v = some (d.ifindex, fun q => if ctx.slot = q then some key else d.keypairs[q]?) ∧
      key.internalId = w.k.keypairCounter+1 ∧ key.peer = ctx.word ∧ key.receiving.isValid = true := by
  obtain ⟨read,init,derive,entered,_,hi,hb,hr,_⟩ := SessionOrigin.front_material _ _ _ _ hr
  obtain ⟨d,hd,hp,hs,hw,hslot,hread⟩ := entered_peer _ _ _ _ entered
  obtain ⟨dev,old,hdev,hold,hinit⟩ := initKey_effect _ _ _ _ _ hi
  have ed : dev = keyAllocationDevice d (w.k.keypairCounter+1) ctx.word := by
    apply Option.some.inj
    simpa [hread,keyAllocationWorld] using hdev.symm
  subst dev
  have eold : old = ({internalId := w.k.keypairCounter+1, peer := ctx.word} : Keypair) := by
    simpa [keyAllocationDevice,hslot] using hold.symm
  subst old
  have hb := sameKernel_branch _ _ init ctx.initiator derive hb
  obtain ⟨dev,key,result,hdev,hkey,hresult,hstamp,hword,hvalid⟩ := derive_effect _ _ _ _ _ hr
  have ed : dev = {keyAllocationDevice d (w.k.keypairCounter+1) ctx.word with
      keypairs := (keyAllocationDevice d (w.k.keypairCounter+1) ctx.word).keypairs.insert ctx.slot
        {internalId := w.k.keypairCounter+1, peer := ctx.word,
         iAmTheInitiator := ctx.state == HANDSHAKE_CONSUMED_RESPONSE, remoteIndex := ctx.peer.remoteIndex}} := by
    exact Option.some.inj (hdev.symm.trans (by simpa [hb] using hinit))
  subst dev
  simp only [Std.TreeMap.getElem?_insert_self, Option.some.injEq] at hkey
  subst key
  refine ⟨d,result,hd,hp,hs,hw,hslot,?_,hstamp,hword,hvalid⟩
  simp only [view,hresult,Option.map_some]
  apply congrArg some
  apply Prod.ext (by rfl)
  funext q
  by_cases he : ctx.slot = q
  · subst q; simp
  · simp [keyAllocationDevice,←hslot,Std.TreeMap.getElem?_insert, Std.LawfulEqOrd.compare_eq_iff_eq,he]

theorem front_none (pid : PeerId) (w v : World)
    (hr : (SessionOrigin.front pid).run w = .ok (none,v)) : v.k = w.k := by
  unfold SessionOrigin.front SessionOrigin.frontWith at hr
  rw [bind_ok] at hr
  obtain ⟨p,a,hp,hr⟩ := hr
  obtain ⟨ha,_,_,_⟩ := getPeer_return _ _ _ _ hp
  subst a
  rw [bind_ok] at hr
  obtain ⟨reject,b,hb,hr⟩ := hr
  have kb := sessionStateRejected_sameKernel _ w reject b hb
  cases reject with
  | true => simp at hr; subst v; exact kb
  | false =>
    simp only [Bool.false_eq_true,↓reduceIte,bind_ok] at hr
    obtain ⟨word,c,hw,created,d,hc,missing,e,hm,hr⟩ := hr
    have kc := indexOwner_peerWord_sameKernel (.handshake pid) b word c hw
    have he : missing = created.isNone ∧ e = CounterWindow.record d .sessionNoKeypair created.isNone := by
      simpa [CounterWindow.branch_run,eq_comm] using hm
    obtain ⟨rfl,rfl⟩ := he
    cases created with
    | none =>
      simp at hr
      subst v
      exact (create_none _ _ _ hc).trans (kc.trans kb)
    | some id =>
      simp only [Option.isNone_some,Bool.false_eq_true,↓reduceIte,bind_ok] at hr
      obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,he⟩ := hr
      simp at he

/-- The support update occurs at normal front completion, before the session
suffix. The existing valid history can have arbitrary local provenance. -/
theorem front_installs (pid : PeerId) (w v : World) (result : Option SessionOrigin.Context)
    (history : List SessionOrigin.Receipt) (hi : Inv history w)
    (hr : (SessionOrigin.front pid).run w = .ok (result,v)) :
    Inv (history ++ [.material pid ⟨result,w,v⟩]) v := by
  cases result with
  | none =>
    have hk := front_none pid w v hr
    have hv : view v = view w := by simp [view,hk]
    exact InvView.mono (hv ▸ hi) (fun r h => List.mem_append_left _ h)
  | some ctx =>
    obtain ⟨d,key,hd,hp,hs,hw,hslot,hview,hstamp,hword,hvalid⟩ := front_effect _ _ _ _ hr
    intro epoch keys hv id k hk valid
    rw [hview] at hv
    cases hv
    by_cases he : ctx.slot = id
    · subst id
      simp only [↓reduceIte,Option.some.injEq] at hk
      subst k
      obtain ⟨dev,hdev⟩ : ∃ dev, v.k.wg = some dev := by
        cases h : v.k.wg with
        | none => simp [view,h] at hview
        | some dev => exact ⟨dev,rfl⟩
      have fields : (d.ifindex, fun q => if ctx.slot = q then some key else d.keypairs[q]?) =
          (dev.ifindex, fun q => dev.keypairs[q]?) := by
        simpa [view,hdev] using hview.symm
      have epoch : dev.ifindex = d.ifindex := (congrArg Prod.fst fields).symm
      have keyeq : dev.keypairs[ctx.slot]? = some key := by
        have h := congrFun (congrArg Prod.snd fields) ctx.slot
        simpa using h.symm
      exact ⟨pid,⟨some ctx,w,v⟩,ctx,dev,key,by simp,hr,rfl,rfl,hdev,epoch,keyeq,hvalid,hword,rfl,Or.inr hword⟩
    · have old : d.keypairs[id]? = some k := by simpa [he] using hk
      exact (hi d.ifindex (fun q => d.keypairs[q]?) (by simp [view,hd]) id k old valid).mono
        (fun r h => List.mem_append_left _ h)

def receipt? : MaterialOrigin.Event R → Option R
  | .life _ => none | .receipt r => some r

def SessionInv (h : List (MaterialOrigin.Event SessionOrigin.Receipt)) (w : World) : Prop :=
  MaterialOrigin.Valid SessionOrigin.Receipt.Valid h ∧ Inv (h.filterMap receipt?) w

theorem access_receipts (a : MixedM α) (w : World) (h : List (MaterialOrigin.Event R)) :
    (runPrefix (MaterialOrigin.access a) w h).2.filterMap receipt? = h.filterMap receipt? := by
  exact focusPrefix_other _ _ receipt? (fun _ => rfl) a w h

theorem access_support (a : MixedM α) (original : M α)
    (he : ErasesPrefix a original)
    (retain : ∀ w x v, original.run w = .ok (x,v) → Retains w v) :
    PrefixPreserves SessionInv (MaterialOrigin.Valid SessionOrigin.Receipt.Valid)
      (MaterialOrigin.access a) := by
  intro w h hi
  obtain ⟨suffix,hs,hv,_⟩ := access_valid a SessionOrigin.Receipt.Valid w h hi.1
  refine ⟨suffix,hs,hv,?_⟩
  cases hr : (runPrefix (MaterialOrigin.access a) w h).1 with
  | error e => trivial
  | ok out =>
    refine ⟨hv,?_⟩
    rw [access_receipts]
    exact hi.2.retain (retain w out.1 out.2 ((access_erases he w h).symm.trans hr))

theorem front_observer_support (pid : PeerId) :
    PrefixEnsures SessionInv (MaterialOrigin.Valid SessionOrigin.Receipt.Valid)
      (receiptObserved (SessionOrigin.observedFront pid)
        (MaterialOrigin.Event.receipt ∘ SessionOrigin.Receipt.material pid))
      (fun _ => SessionInv) := by
  intro w h hi
  obtain ⟨s,hs,hv,_⟩ := SessionOrigin.observedFront_valid pid w h hi.1
  rw [runPrefix_receiptObserved]
  cases hr : runPrefix (SessionOrigin.observedFront pid) w h with
  | mk result t =>
    simp only [hr] at hs hv
    cases result with
    | error e => exact ⟨s,hs,hv,trivial⟩
    | ok out =>
      rcases out with ⟨result,v⟩
      have run : (SessionOrigin.front pid).run w = .ok (result,v) :=
        (SessionOrigin.observedFront_erases pid w h).symm.trans (congrArg Prod.fst hr)
      have truth : MaterialOrigin.Valid SessionOrigin.Receipt.Valid
          (t ++ [.receipt (.material pid ⟨result,w,v⟩)]) := by
        intro e he
        rcases List.mem_append.mp he with he | he
        · exact hv e he
        · simp only [List.mem_singleton] at he
          subst e
          exact run
      have supported := front_installs pid w v result (h.filterMap receipt?) hi.2 run
      refine ⟨s ++ [.receipt (.material pid ⟨result,w,v⟩)],by simp [hs,List.append_assoc],truth,truth,?_⟩
      apply supported.mono
      intro r hm
      simp only [List.mem_append,List.mem_singleton] at hm
      rcases hm with hm | rfl
      · rw [hs]
        simp only [List.filterMap_append,List.mem_append]
        exact Or.inl (Or.inl hm)
      · simp [receipt?]

theorem session_support (pid : PeerId) :
    PrefixPreserves SessionInv (MaterialOrigin.Valid SessionOrigin.Receipt.Valid)
      (SessionOrigin.observed pid) := by
  unfold SessionOrigin.observed
  apply PrefixEnsures.preserves
  apply PrefixEnsures.bind (front_observer_support pid)
  intro result
  cases result with
  | none => exact PrefixEnsures.pure (fun _ _ h => h.1) (fun _ _ h => h)
  | some ctx =>
    exact access_support (SessionOrigin.tailPrefix pid ctx.slot) (SessionOrigin.tail pid ctx.slot)
      (SessionOrigin.tail_erases _ _) (fun w x v hr => tail_retains pid ctx.slot hr)

/-- A local join with the actual stored packet and successful AEAD result.
Support is required at this run's entry; it supplies no initialized provenance. -/
theorem decrypt_supported (history : List SessionOrigin.Receipt) (id : SkbId)
    (r : RunWitness (RxPacket × Option RxPacket)) (out : RxPacket)
    (hi : Inv history r.before) (hr : r.Valid (RxOrigin.readDecrypt id)) (ho : r.value.2 = some out) :
    ∃ d k, r.before.k.wg = some d ∧ d.rxSkbs[id]? = some r.value.1 ∧
      d.keypairs[r.value.1.keypair]? = some k ∧ Supported history d.ifindex r.value.1.keypair k ∧
      (decryptPacket r.value.1).run r.before = .ok (some out,r.after) ∧
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

def localSession (pid : PeerId) : PrefixM Event Bool :=
  focusPrefix sessionEncode sessionDecode (SessionOrigin.observed pid)

def localDecrypt (id : SkbId) : PrefixM Event (RxPacket × Option RxPacket) :=
  focusPrefix rxEncode rxDecode (RxOrigin.decrypt id)

theorem localSession_erases (pid : PeerId) : ErasesPrefix (localSession pid) (beginSession pid) :=
  focusPrefix_erases _ _ (SessionOrigin.observed_erases pid)

theorem localDecrypt_erases (id : SkbId) : ErasesPrefix (localDecrypt id) (RxOrigin.readDecrypt id) :=
  focusPrefix_erases _ _ (RxOrigin.decrypt_erases id)

theorem session_filter (h : List Event) :
    (h.filterMap sessionDecode).filterMap receipt? = sessions h := by
  induction h with
  | nil => rfl
  | cons e h ih => cases e <;> simp [sessionDecode,receipt?,sessions,sessionReceipt] at * <;> exact ih

theorem localSession_support (pid : PeerId) :
    PrefixPreserves
      (fun h w => MaterialOrigin.Valid SessionOrigin.Receipt.Valid (h.filterMap sessionDecode) ∧ Inv (sessions h) w)
      (fun h => MaterialOrigin.Valid SessionOrigin.Receipt.Valid (h.filterMap sessionDecode))
      (localSession pid) := by
  have h := PrefixEnsures.focus sessionEncode sessionDecode (by intro e; cases e <;> rfl)
    (show PrefixEnsures SessionInv (MaterialOrigin.Valid SessionOrigin.Receipt.Valid)
      (SessionOrigin.observed pid) (fun _ => SessionInv) from session_support pid)
  simpa only [SessionInv,session_filter,localSession] using h.preserves

theorem sessionSource_appends (pid : PeerId) : Appends (SessionOrigin.observed pid) := by
  unfold SessionOrigin.observed SessionOrigin.observedFront SessionOrigin.frontWith
  simp only [SessionOrigin.allocate,MaterialOrigin.access]
  repeat' first
    | with_reducible exact Appends.focus _ _ _
    | with_reducible exact Appends.lift _
    | with_reducible exact Appends.pure _
    | with_reducible apply Appends.receiptObserved
    | with_reducible apply Appends.bind
    | (intro_forall; try dsimp only)
    | split

/-- The local adapter retains the exact incoming lifetime history and all
failed-prefix accesses. No material-support premise is added to R2 projection. -/
theorem adapter_projects (encode : MaterialOrigin.Event R → Event)
    (decode : Event → Option (MaterialOrigin.Event R))
    (hin : ∀ e, (decode e).bind MaterialOrigin.life? = lifetime e)
    (hout : ∀ e, lifetime (encode e) = MaterialOrigin.life? e)
    (g : PrefixM (MaterialOrigin.Event R) α) (a : MixedM α)
    (ha : Appends g) (hp : ProjectsUnder AllocationInv MaterialOrigin.life? g a) :
    ProjectsUnder AllocationInv lifetime (focusPrefix encode decode g) a := by
  intro w h hi
  have input : (h.filterMap decode).filterMap MaterialOrigin.life? = h.filterMap lifetime := by
    simp only [List.filterMap_filterMap]
    congr 1
    funext e
    exact hin e
  have projected := hp w (h.filterMap decode) (by simpa [input] using hi)
  obtain ⟨s,hs⟩ := ha w (h.filterMap decode)
  have equation : runPrefix g w (h.filterMap decode) =
      ((runPrefix g w (h.filterMap decode)).1,h.filterMap decode ++ s) := Prod.ext rfl hs
  rw [focusPrefix_suffix encode decode g w h _ s equation]
  have output : (s.map encode).filterMap lifetime = s.filterMap MaterialOrigin.life? := by
    simp only [List.filterMap_map]
    congr 1
    funext e
    exact hout e
  simpa only [hs,input,List.filterMap_append,output] using projected

theorem localSession_projects (pid : PeerId) :
    ProjectsUnder AllocationInv lifetime (localSession pid) (beginSessionPrefix pid) :=
  adapter_projects _ _ (by intro e; cases e <;> rfl) (by intro e; cases e <;> rfl)
    _ _ (sessionSource_appends pid) (SessionOrigin.observed_projects pid)

theorem localDecrypt_projects (id : SkbId) :
    ProjectsUnder AllocationInv lifetime (localDecrypt id) (RxOrigin.readDecryptPrefix id) :=
  adapter_projects _ _ (by intro e; cases e <;> rfl) (by intro e; cases e <;> rfl)
    _ _ ((Appends.focus _ _ _).receiptObserved) (RxOrigin.decrypt_projects id)

theorem rx_lifetime (h : List Event) :
    (h.filterMap rxDecode).filterMap MaterialOrigin.life? = h.filterMap lifetime := by
  simp only [List.filterMap_filterMap]
  congr 1
  funext e
  cases e <;> rfl

/-- Exact local execution equation. The original RX observer executes once at
its actual projected incoming lifetime history. Stop emits no successful run. -/
theorem localDecrypt_run (id : SkbId) (w : World) (h : List Event) :
    let out := runPrefix (RxOrigin.readDecryptPrefix id) w (h.filterMap lifetime)
    let suffix := (out.2.drop (h.filterMap lifetime).length).map Event.life
    runPrefix (localDecrypt id) w h = match out.1 with
      | .error e => (.error e,h ++ suffix)
      | .ok (result,v) => (.ok (result,v),h ++ suffix ++ [.rx (.decrypt id ⟨result,w,v⟩)]) := by
  have ha : runPrefix (MaterialOrigin.access (RxOrigin.readDecryptPrefix id)) w (h.filterMap rxDecode) =
      ((runPrefix (RxOrigin.readDecryptPrefix id) w (h.filterMap lifetime)).1,
        h.filterMap rxDecode ++
          ((runPrefix (RxOrigin.readDecryptPrefix id) w (h.filterMap lifetime)).2.drop
            (h.filterMap lifetime).length).map MaterialOrigin.Event.life) := by
    change ((runPrefix (RxOrigin.readDecryptPrefix id) w ((h.filterMap rxDecode).filterMap MaterialOrigin.life?)).1,
      h.filterMap rxDecode ++
        ((runPrefix (RxOrigin.readDecryptPrefix id) w ((h.filterMap rxDecode).filterMap MaterialOrigin.life?)).2.drop
          ((h.filterMap rxDecode).filterMap MaterialOrigin.life?).length).map MaterialOrigin.Event.life) = _
    rw [rx_lifetime]
  dsimp only
  unfold localDecrypt
  change ((runPrefix (RxOrigin.decrypt id) w (h.filterMap rxDecode)).1,
    h ++ ((runPrefix (RxOrigin.decrypt id) w (h.filterMap rxDecode)).2.drop (h.filterMap rxDecode).length).map rxEncode) = _
  rw [RxOrigin.decrypt,runPrefix_receiptObserved,ha]
  cases hr : runPrefix (RxOrigin.readDecryptPrefix id) w (h.filterMap lifetime) with
  | mk result t =>
    cases result with
    | error e => simp [List.map_map,Function.comp_def,rxEncode]
    | ok out =>
      rcases out with ⟨result,v⟩
      simp [List.map_map,Function.comp_def,rxEncode,List.append_assoc]

/-- A successful new decrypt receipt follows its material witness strictly in
this same local journal. The incoming support premise is explicit: arbitrary
input receipts need not be reached occurrences of an initialized Runner. -/
theorem localDecrypt_origin (id : SkbId) (w : World) (h : List Event)
    (packet out : RxPacket) (v : World)
    (hi : Inv (sessions h) w)
    (hr : (runPrefix (localDecrypt id) w h).1 = .ok ((packet,some out),v)) :
    ∃ (suffix : List LifetimeEvent) (d : Device) (k : Keypair) (pid : PeerId)
      (r : RunWitness (Option SessionOrigin.Context)) (ctx : SessionOrigin.Context)
      (originDev : Device) (original : Keypair) (before middle : List Event),
      (runPrefix (localDecrypt id) w h).2 =
        h ++ suffix.map Event.life ++ [.rx (.decrypt id ⟨(packet,some out),w,v⟩)] ∧
      h = before ++ [.session (.material pid r)] ++ middle ∧
      r.Valid (SessionOrigin.front pid) ∧ r.value = some ctx ∧ ctx.slot = packet.keypair ∧
      r.after.k.wg = some originDev ∧ originDev.ifindex = d.ifindex ∧
      originDev.keypairs[packet.keypair]? = some original ∧ original.receiving.isValid = true ∧
      original.peer = ctx.word ∧ material k = material original ∧ WordLe k.peer ctx.word ∧
      w.k.wg = some d ∧ d.rxSkbs[id]? = some packet ∧ d.keypairs[packet.keypair]? = some k ∧
      (decryptPacket packet).run w = .ok (some out,v) ∧
      out = {packet with nonce := u64le packet.bytes 8, bytes := out.bytes} ∧
      aeadDecrypt k.receiving.key (counterNonce (u64le packet.bytes 8)) (packet.bytes.drop 16) [] = some out.bytes := by
  have original : (RxOrigin.readDecrypt id).run w = .ok ((packet,some out),v) :=
    (localDecrypt_erases id w h).symm.trans hr
  obtain ⟨d,k,hd,hp,hk,support,hdc,record,aead⟩ :=
    decrypt_supported (sessions h) id ⟨(packet,some out),w,v⟩ out hi original rfl
  obtain ⟨pid,r,ctx,originDev,old,mem,hv,hctx,hslot,ho,he,hkey,hvalid,hword,hmat,keep⟩ := support
  obtain ⟨event,hm,hevent⟩ := List.mem_filterMap.mp mem
  have eventEq : event = .session (.material pid r) := by
    cases event <;> simp only [sessionReceipt,Option.some.injEq,reduceCtorEq] at hevent
    subst hevent
    rfl
  subst event
  obtain ⟨before,middle,hist⟩ := List.mem_iff_append.mp hm
  have observed : (runPrefix (RxOrigin.readDecryptPrefix id) w (h.filterMap lifetime)).1 =
      .ok ((packet,some out),v) := (RxOrigin.readDecrypt_erases id w _).trans original
  refine ⟨(runPrefix (RxOrigin.readDecryptPrefix id) w (h.filterMap lifetime)).2.drop (h.filterMap lifetime).length,d,k,pid,r,ctx,originDev,old,before,middle,?_,?_,hv,hctx,hslot,ho,he,hkey,hvalid,hword,hmat,keep,hd,hp,hk,hdc,record,aead⟩
  · rw [localDecrypt_run,observed]
  · simpa [List.append_assoc] using hist

theorem create_retains (word : Option PeerId) (w v : World) (result : Option KeypairId)
    (hr : (keypairCreate word).run w = .ok (result,v)) : Retains w v := by
  cases result with
  | none =>
    have hk := create_none word w v hr
    unfold Retains
    simp only [view,hk]
    exact RetainsView.refl _
  | some id =>
    obtain ⟨d,hd,hid,hv⟩ := create_some word w v id hr
    have retain := retains_insert d.ifindex (fun q => d.keypairs[q]?) d.nextKeypairId
      ({internalId := w.k.keypairCounter+1, peer := word} : Keypair) (by intro bad; cases bad)
    simpa [Retains,view,hv,keyAllocationWorld,keyAllocationDevice,hd,
      Std.TreeMap.getElem?_insert,Std.LawfulEqOrd.compare_eq_iff_eq] using retain

theorem receiveReject_kernel (k : Keypair) : SameKernel (KeyTimes.receiveReject k) := by
  apply sameKernel_of_wp
  intro original
  have ht := sameKernel_wp _ (branchExpired_sameKernel .decKeyExpired k.receiving.birthdate REJECT_AFTER_TIME)
    (fun s => s = original)
  mvcgen [KeyTimes.receiveReject,WG.orM,branch,branchCmp,ht]

theorem receiveTail_kernel (pkt : RxPacket) (k : Keypair) : SameKernel (KeyTimes.receiveTail pkt k) := by
  apply sameKernel_of_wp
  intro original
  have ha := sameKernel_wp _ (hiddenAlloc_sameKernel .skbCowDataRx) (fun s => s = original)
  mvcgen [KeyTimes.receiveTail,WG.orM,branch,invariant,ha]

theorem decrypt_spec (P : View → Prop) (stable : Stable P) (pkt : RxPacket) :
    ⦃fun w => ⌜P (view w)⌝⦄ decryptPacket pkt ⦃⇓? _ w => ⌜P (view w)⌝⦄ := by
  rw [KeyTimes.decryptPacket_factor]
  have hg := getKeypair_spec P
  have hs := setKeypair_spec P stable
  have hr := fun k => (kernel (receiveReject_kernel k)).wp P
  have ht := fun k => (kernel (receiveTail_kernel pkt k)).wp P
  mvcgen [hg,hs,hr,ht,branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [view]

theorem readDecrypt_retains (id : SkbId) (w v : World) (result : RxPacket × Option RxPacket)
    (hr : (RxOrigin.readDecrypt id).run w = .ok (result,v)) : Retains w v := by
  have hg : SameView view (getRxSkb id) := by
    apply SameView.of_wp
    intro s
    mvcgen [getRxSkb,getDev,getK,invariant]
  have hs : ⦃fun u => ⌜RetainsView (view w) (view u)⌝⦄ RxOrigin.readDecrypt id
      ⦃⇓? _ u => ⌜RetainsView (view w) (view u)⌝⦄ := by
    have hp := hg.wp (RetainsView (view w))
    have hd := decrypt_spec (RetainsView (view w)) (fun _ _ a b => b.trans a)
    mvcgen [RxOrigin.readDecrypt,hp,hd]
  exact (hoare_iff_triple _ _ _).mpr hs w result v (RetainsView.refl _) hr

theorem localDecrypt_support (id : SkbId) :
    PrefixPreserves (fun h w => Inv (sessions h) w) (fun _ => True) (localDecrypt id) := by
  intro w h hi
  obtain ⟨suffix,hs⟩ := Appends.focus rxEncode rxDecode (RxOrigin.decrypt id) w h
  refine ⟨suffix,hs,trivial,?_⟩
  cases hr : (runPrefix (localDecrypt id) w h).1 with
  | error e => trivial
  | ok out =>
    have history : sessions (runPrefix (localDecrypt id) w h).2 = sessions h :=
      focusPrefix_other rxEncode rxDecode sessionReceipt (by intro e; cases e <;> rfl) _ w h
    change Inv (sessions (runPrefix (localDecrypt id) w h).2) out.2
    rw [history]
    exact hi.retain (readDecrypt_retains id w out.2 out.1 ((localDecrypt_erases id w h).symm.trans hr))

/-- Truth of supplied and newly emitted receipts, independent of R2's access
invariant. Life events are accounted for by the separate exact R2 projection. -/
def Event.Valid : Event → Prop
  | .life _ => True
  | .session r => SessionOrigin.Receipt.Valid r
  | .rx r => RxOrigin.Receipt.Valid r

def Valid (h : List Event) : Prop := ∀ e ∈ h, e.Valid

theorem focus_valid (encode : E → Event) (decode : Event → Option E)
    (valid : E → Prop) (g : PrefixM E α)
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
    PrefixPreserves (fun h _ => Valid h) Valid (localSession pid) := by
  apply focus_valid sessionEncode sessionDecode
    (fun e => match e with | .life _ => True | .receipt r => SessionOrigin.Receipt.Valid r)
    (SessionOrigin.observed pid)
  · intro e x hv hx
    cases e <;> simp only [sessionDecode,Option.some.injEq,reduceCtorEq] at hx
    all_goals subst x; exact hv
  · intro e hv; cases e <;> exact hv
  · intro w h hi
    have input : MaterialOrigin.Valid SessionOrigin.Receipt.Valid h := by
      intro e he; cases e <;> exact hi _ he
    obtain ⟨s,hs,hv,hq⟩ := SessionOrigin.observed_valid pid w h input
    have truth : ∀ e ∈ (runPrefix (SessionOrigin.observed pid) w h).2,
        (match e with | .life _ => True | .receipt r => SessionOrigin.Receipt.Valid r) := by
      intro e he; cases e <;> exact hv _ he
    refine ⟨s,hs,truth,?_⟩
    cases (runPrefix (SessionOrigin.observed pid) w h).1 <;> first | trivial | exact truth

theorem localDecrypt_valid (id : SkbId) :
    PrefixPreserves (fun h _ => Valid h) Valid (localDecrypt id) := by
  apply focus_valid rxEncode rxDecode
    (fun e => match e with | .life _ => True | .receipt r => RxOrigin.Receipt.Valid r)
    (RxOrigin.decrypt id)
  · intro e x hv hx
    cases e <;> simp only [rxDecode,Option.some.injEq,reduceCtorEq] at hx
    all_goals subst x; exact hv
  · intro e hv; cases e <;> exact hv
  · intro w h hi
    have input : MaterialOrigin.Valid RxOrigin.Receipt.Valid h := by
      intro e he; cases e <;> exact hi _ he
    obtain ⟨s,hs,hv,hq⟩ := RxOrigin.decrypt_valid id w h input
    have truth : ∀ e ∈ (runPrefix (RxOrigin.decrypt id) w h).2,
        (match e with | .life _ => True | .receipt r => RxOrigin.Receipt.Valid r) := by
      intro e he; cases e <;> exact hv _ he
    refine ⟨s,hs,truth,?_⟩
    cases (runPrefix (RxOrigin.decrypt id) w h).1 <;> first | trivial | exact truth

end Leanux.Proofs.WG.Origins
