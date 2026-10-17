import Leanux.Proofs.WG.Peers.ConfiguredIdentity
import Leanux.Proofs.WG.Origins.SessionMaterial

/-! Configured support is a separate product over the existing session receipts.
A derivation-front receipt alone is not a successful whole session. The actual
normal tail supplies liveness and a non-NULL self word; no Noise authenticity
or initialized configured registry is asserted. -/
namespace Leanux.Proofs.WG.ConfiguredSession
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open MaterialOrigin Lifetimes
set_option pp.structureInstances false

theorem create_view (word : Option PeerId) : SameView ConfiguredIdentity.view (keypairCreate word) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hr
  cases result with
  | none => exact congrArg ConfiguredIdentity.view (Origins.create_none _ _ _ _ _ hr)
  | some id =>
    obtain ⟨d,hd,hid,hv⟩ := Origins.create_some _ _ _ _ _ _ hr
    simp [ConfiguredIdentity.view,hv,keyAllocationWorld,keyAllocationDevice,hd,ConfiguredIdentity.state]

theorem derive_view (id : KeypairId) (initiator : Bool) (ck : List UInt8) :
    SameView ConfiguredIdentity.view (deriveKeys id initiator ck) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hr
  cases x
  obtain ⟨d,old,key,hd,hk,hv,rest⟩ := Origins.derive_effect _ _ _ _ _ _ _ hr
  simp [ConfiguredIdentity.view,hv,hd,ConfiguredIdentity.state]

theorem init_view (id : KeypairId) (b : Bool) (remote : Nat) :
    SameView ConfiguredIdentity.view (SessionOrigin.initKey id b remote) := by
  unfold SessionOrigin.initKey
  apply SameView.bind (ConfiguredIdentity.getKeypair_view id)
  intro k
  exact ConfiguredIdentity.setKeypair_view id _

theorem front_view (pid : PeerId) : SameView ConfiguredIdentity.view (SessionOrigin.front pid) := by
  have hg (q : PeerId) : SameView ConfiguredIdentity.view (getPeer q) := by
    intro initial
    exact hoare_consequence (ConfiguredIdentity.getPeer_spec (fun t => t = initial) q)
      (fun _ h => h) (fun _ _ h => h.1)
  have ha {α : Type} (a : AmbientM α) :
      SameView ConfiguredIdentity.view (StateT.lift a : WG.M α) :=
    fun initial => hoare_liftAmbient a (fun w => ConfiguredIdentity.view w = initial)
  unfold SessionOrigin.front SessionOrigin.frontWith
  apply SameView.bind (hg pid)
  intro p
  apply SameView.bind (ha (sessionStateRejected p.handshakeState))
  intro rejected
  split
  · exact SameView.pure _ _
  · apply SameView.bind (fun initial =>
      indexOwner_peerWord_preserves (.handshake pid) (fun w => ConfiguredIdentity.view w = initial))
    intro word
    apply SameView.bind (create_view word)
    intro created
    apply SameView.bind (ha (AmbientM.branch .sessionNoKeypair created.isNone))
    intro missing
    split
    · exact SameView.pure _ _
    · cases created with
      | none => exact ha (AmbientM.invariant "unreachable")
      | some kp =>
        apply SameView.bind (hg pid)
        intro peer
        apply SameView.bind (init_view kp (p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE) peer.remoteIndex)
        intro _
        apply SameView.bind (ha (AmbientM.branch .sessionInitiator
          (p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE)))
        intro direction
        apply SameView.bind (derive_view kp direction peer.chainingKey)
        intro _
        exact SameView.pure _ _



theorem tail_view (pid kp : Nat) : SameView ConfiguredIdentity.view (SessionOrigin.tail pid kp) := by
  have hg : SameView ConfiguredIdentity.view (getPeer pid) := by
    intro initial
    exact hoare_consequence (ConfiguredIdentity.getPeer_spec (fun t => t = initial) pid)
      (fun _ h => h) (fun _ _ h => h.1)
  have ha {α : Type} (a : AmbientM α) :
      SameView ConfiguredIdentity.view (StateT.lift a : WG.M α) :=
    fun initial => hoare_liftAmbient a (fun w => ConfiguredIdentity.view w = initial)
  unfold SessionOrigin.tail SessionOrigin.tailWith
  apply SameView.bind (ConfiguredIdentity.handshakeZero_view pid)
  intro _
  apply SameView.bind hg
  intro p
  apply SameView.bind (ha (AmbientM.branch .sessionAlive (!p.isDead)))
  intro alive
  split
  · apply SameView.bind (ConfiguredIdentity.addNewKeypair_view pid kp)
    intro _
    apply SameView.bind (fun initial =>
      indexOwner_peerDeref_preserves (.handshake pid) (fun w => ConfiguredIdentity.view w = initial))
    intro _
    apply SameView.bind (fun initial => hoare_liftIndex (indexReplaceHandshake pid kp)
      (fun w => ConfiguredIdentity.view w = initial) (by
        intro g d table hg hd
        simpa only [ConfiguredIdentity.view,hd,Option.map_some,ConfiguredIdentity.state] using hg))
    intro replaced
    split
    · exact ha (AmbientM.unsupported "begin_session: the handshake entry was unhashed")
    · exact SameView.pure _ _
  · exact ha (AmbientM.unsupported "a dead peer finishing a session")

/-- Actual non-NULL dereference, preserving the entry configured view. -/
theorem deref_spec (pid : PeerId) (P : Option ConfiguredIdentity.State → Prop) :
    ⦃fun w => ⌜P (ConfiguredIdentity.view w)⌝⦄ IndexOwner.peerDeref (.handshake pid)
    ⦃⇓? result w => ⌜P (ConfiguredIdentity.view w) ∧
      ∃ s p, ConfiguredIdentity.view w = some s ∧ s.peers pid = some p ∧ p.word = some result⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hp hr
  simp only [IndexOwner.peerDeref, IndexOwner.peerWord, bind_assoc, pure_bind] at hr
  rw [bind_ok_ambient] at hr
  obtain ⟨p, u, middle, hg, hr⟩ := hr
  obtain ⟨rfl, rfl, d, hd, hresident⟩ := Origins.getPeer_return _ _ _ _ _ _ hg
  cases hw : p.handshakeEntryPeer with
  | none => simp [hw, unsupported, AmbientM.unsupported] at hr; cases hr
  | some owner =>
    simp only [hw, StateT.run_pure, CounterWindow.except_pure,
      Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hr
    exact ⟨hp, ConfiguredIdentity.state d, ConfiguredIdentity.cell p,
      by simp [ConfiguredIdentity.view,hd],
      by simp [ConfiguredIdentity.state,hresident], hw⟩

/-- A normal tail really passed the live-peer test and non-NULL handshake
owner dereference; neither is inferred merely from a Some front receipt. -/
theorem tail_live (pid kp : Nat) (w v : WGWorld) (result : Bool)
    (ambient ambient' : Ambient)
    (hr : ((SessionOrigin.tail pid kp).run w).run ambient = .ok ((result,v),ambient')) :
    ∃ s p, ConfiguredIdentity.view w = some s ∧ s.peers pid = some p ∧
      p.dead = false ∧ p.word.isSome = true := by
  unfold SessionOrigin.tail SessionOrigin.tailWith at hr
  rw [bind_ok_ambient] at hr
  obtain ⟨z,a,aAmbient,hzero,hr⟩ := hr
  cases z
  rw [bind_ok_ambient] at hr
  obtain ⟨p,b,bAmbient,hget,hr⟩ := hr
  obtain ⟨hba,hambient,dev,hdev,hp⟩ := Origins.getPeer_return _ _ _ _ _ _ hget
  subst b
  subst bAmbient
  rw [bind_ok_ambient] at hr
  obtain ⟨alive,c,cAmbient,hbranch,hr⟩ := hr
  have hb : alive = !p.isDead ∧ c = a ∧
      cAmbient = CounterWindow.record aAmbient .sessionAlive (!p.isDead) := by
    simpa [branch,CounterWindow.branch_run,eq_comm,and_assoc] using hbranch
  obtain ⟨halive,hc,hambient⟩ := hb
  subst alive
  subst c
  subst cAmbient
  cases dead : p.isDead with
  | true => simp [dead,unsupported,AmbientM.unsupported] at hr; cases hr
  | false =>
    simp only [dead,Bool.not_false,↓reduceIte,bind_ok_ambient] at hr
    obtain ⟨z,d,dAmbient,hrotate,q,e,eAmbient,hderef,rest⟩ := hr
    cases z
    have hz := (ProjectedAction.iff_run_ambient _ _ _).mp
      (ConfiguredIdentity.handshakeZero_view pid) w ambient () a aAmbient hzero
    have hv : ConfiguredIdentity.view d = ConfiguredIdentity.view w :=
      ((ProjectedAction.iff_run_ambient _ _ _).mp
        (ConfiguredIdentity.addNewKeypair_view pid kp) a
          (CounterWindow.record aAmbient .sessionAlive true) () d dAmbient hrotate).trans hz
    have facts := (hoare_iff_run_ambient _ _ _).mp
      (deref_spec pid (fun t => t = ConfiguredIdentity.view w)) d dAmbient q e eAmbient hv hderef
    obtain ⟨he,s,x,hs,hx,hword⟩ := facts
    have hw : ConfiguredIdentity.view w = some (ConfiguredIdentity.state dev) :=
      hz.symm.trans (by simp [ConfiguredIdentity.view,hdev])
    have es : s = ConfiguredIdentity.state dev := Option.some.inj (hs.symm.trans (he.trans hw))
    subst s
    have ex : x = ConfiguredIdentity.cell p := Option.some.inj
      (hx.symm.trans (by simp [ConfiguredIdentity.state,hp]))
    subst x
    exact ⟨ConfiguredIdentity.state dev,ConfiguredIdentity.cell p,hw,
      by simp [ConfiguredIdentity.state,hp],dead,by simp [hword]⟩

/-- The same full peer record at this actual front's entry supplies the table
row, allocation stamp and configured static key. Later raw-slot identity is a
separate obligation. -/
def Configured (pid : PeerId) (w : WGWorld) (ctx : SessionOrigin.Context) : Prop :=
  ∃d,w.dev=some d ∧ d.peers[pid]?=some ctx.peer ∧
    (ctx.peer.remoteStatic,pid)∈d.peerHashtable ∧ ctx.peer.isDead=false ∧ ctx.word=some pid

theorem front_configured (pid : PeerId) (ctx : SessionOrigin.Context) (w u v : WGWorld)
    (ambient middle ambient' : Ambient) (result : Bool) (hi : ConfiguredIdentity.Inv w)
    (hf : ((SessionOrigin.front pid).run w).run ambient = .ok ((some ctx,u),middle))
    (ht : ((SessionOrigin.tail pid ctx.slot).run u).run middle = .ok ((result,v),ambient')) :
    Configured pid w ctx := by
  obtain ⟨d,key,hd,hp,hst,hw,hslot,rest⟩ := Origins.front_effect pid ctx w u ambient middle hf
  obtain ⟨s,p,hs,hcell,alive,nonnull⟩ := tail_live pid ctx.slot u v result middle ambient' ht
  have hview : ConfiguredIdentity.view w = some (ConfiguredIdentity.state d) := by
    simp [ConfiguredIdentity.view,hd]
  have eqs : s = ConfiguredIdentity.state d := Option.some.inj
    (hs.symm.trans (((ProjectedAction.iff_run_ambient _ _ _).mp
      (front_view pid) w ambient (some ctx) u middle hf).trans hview))
  subst s
  have eqp : p = ConfiguredIdentity.cell ctx.peer := Option.some.inj
    (hcell.symm.trans (by simp [ConfiguredIdentity.state,hp]))
  subst p
  have inv := hi _ hview
  have self := inv.self pid (ConfiguredIdentity.cell ctx.peer) (by simp [ConfiguredIdentity.state,hp])
  have word : ctx.word = some pid := by
    rcases self with h | h
    · change ctx.peer.handshakeEntryPeer = none at h
      change ctx.peer.handshakeEntryPeer.isSome = true at nonnull
      simp [h] at nonnull
    · exact hw.trans h
  exact ⟨d,hd,hp,inv.live _ _ (by simp [ConfiguredIdentity.state,hp]) alive (by simp),alive,word⟩

/-- Material, owner and configured identity use one receipt and one Context. -/
def Supported (history : List SessionOrigin.Receipt) (epoch : Nat) (slot : KeypairId) (key : Keypair) : Prop :=
  ∃ (pid : PeerId) (run : WGRunWitness (Option SessionOrigin.Context))
    (ctx : SessionOrigin.Context) (d : Device) (original : Keypair),
    SessionOrigin.Receipt.material pid run∈history ∧ run.Valid (SessionOrigin.front pid) ∧
    run.value=some ctx ∧ ctx.slot=slot ∧ Configured pid run.before ctx ∧
    run.after.dev=some d ∧ d.ifindex=epoch ∧ d.keypairs[slot]?=some original ∧
    original.receiving.isValid=true ∧ original.peer=ctx.word ∧
    material key=material original ∧ Origins.WordLe key.peer ctx.word

def Inv (history : List SessionOrigin.Receipt) (w : WGWorld) : Prop :=
  ∀d,w.dev=some d → ∀id key,d.keypairs[id]?=some key → key.receiving.isValid=true →
    Supported history d.ifindex id key

theorem Supported.original (h : Supported xs epoch slot key) : Origins.Supported xs epoch slot key := by
  obtain ⟨pid,r,ctx,d,k,hm,hr,hv,hs,_,rest⟩:=h
  exact ⟨pid,r,ctx,d,k,hm,hr,hv,hs,rest⟩

theorem Supported.mono (h : Supported xs epoch slot key) (hm : ∀r∈xs,r∈ys) : Supported ys epoch slot key := by
  obtain ⟨pid,r,ctx,d,k,hin,rest⟩:=h
  exact ⟨pid,r,ctx,d,k,hm _ hin,rest⟩

theorem Supported.retain (h : Supported xs epoch slot old) (hk : Origins.KeyLe key old) : Supported xs epoch slot key := by
  obtain ⟨pid,r,ctx,d,k,hm,hr,hv,hs,hc,hd,he,hk',valid,word,mat,keep⟩:=h
  exact ⟨pid,r,ctx,d,k,hm,hr,hv,hs,hc,hd,he,hk',valid,word,hk.1.trans mat,hk.2.trans keep⟩

theorem Inv.mono (h : Inv xs w) (hm : ∀r∈xs,r∈ys) : Inv ys w :=
  fun d hd id k hk valid=>(h d hd id k hk valid).mono hm

theorem Inv.retain (h : Inv xs w) (hr : Origins.Retains w v) : Inv xs v := by
  intro d hd id k hk valid
  obtain ⟨ks,old,hw,ho,vo,le⟩:=hr d.ifindex (fun q=>d.keypairs[q]?)
    (by simp [Origins.view,hd]) id k hk valid
  obtain ⟨before,hbefore,he⟩:=Option.map_eq_some_iff.mp hw
  have ep : before.ifindex=d.ifindex := congrArg Prod.fst he
  have store:=congrFun (congrArg Prod.snd he) id
  have supported:=h before hbefore id old (store.trans ho) vo
  simpa only [ep] using supported.retain le

theorem front_installs (pid : PeerId) (w u : WGWorld) (result : Option SessionOrigin.Context)
    (ambient ambient' : Ambient) (history : List SessionOrigin.Receipt) (hi : Inv history w)
    (hr : ((SessionOrigin.front pid).run w).run ambient = .ok ((result,u),ambient'))
    (configured : ∀ ctx, result = some ctx → Configured pid w ctx) :
    Inv (history ++ [SessionOrigin.Receipt.material pid ⟨result,w,u,ambient,ambient'⟩]) u := by
  cases result with
  | none =>
    have hk := Origins.front_none pid w u ambient ambient' hr
    intro d hd id k hkey valid
    exact (hi d (by simpa [hk] using hd) id k hkey valid).mono
      (fun r h => List.mem_append_left _ h)
  | some ctx =>
    obtain ⟨d,key,hd,hp,hs,hw,hslot,hview,hstamp,hword,hvalid⟩ :=
      Origins.front_effect _ _ _ _ _ _ hr
    intro dev hdev id k hk valid
    have fields : (dev.ifindex,fun q => dev.keypairs[q]?) =
        (d.ifindex,fun q => if ctx.slot = q then some key else d.keypairs[q]?) := by
      simpa [Origins.view,hdev] using hview
    have epoch : dev.ifindex = d.ifindex := congrArg Prod.fst fields
    have keys := congrFun (congrArg Prod.snd fields) id
    dsimp only at keys
    by_cases he : ctx.slot = id
    · subst id
      have ek : k = key := by rw [hk] at keys; simpa using keys
      subst k
      exact ⟨pid,⟨some ctx,w,u,ambient,ambient'⟩,ctx,dev,key,by simp,hr,rfl,rfl,
        configured ctx rfl,hdev,rfl,hk,hvalid,hword,rfl,Or.inr hword⟩
    · have old : d.keypairs[id]? = some k := by simpa [he,hk] using keys.symm
      simpa only [epoch] using (hi d hd id k old valid).mono (fun r h => List.mem_append_left _ h)

/-- Whole normal source decomposition. A stopped tail has no endpoint support
claim, although the unchanged lower observer retains its front receipt. -/
theorem beginSession_support (pid : PeerId) (w v : WGWorld) (result : Bool)
    (ambient ambient' : Ambient) (history : List SessionOrigin.Receipt)
    (configured : ConfiguredIdentity.Inv w) (hi : Inv history w)
    (hr : ((beginSession pid).run w).run ambient = .ok ((result,v),ambient')) :
    ∃ front u middle, ((SessionOrigin.front pid).run w).run ambient = .ok ((front,u),middle) ∧
      Inv (history ++ [SessionOrigin.Receipt.material pid ⟨front,w,u,ambient,middle⟩]) v := by
  rw [SessionOrigin.factor,bind_ok_ambient] at hr
  obtain ⟨front,u,middle,hf,ht⟩ := hr
  refine ⟨front,u,middle,hf,?_⟩
  cases front with
  | none =>
    simp only [StateT.run_pure,CounterWindow.except_pure,Except.ok.injEq,Prod.mk.injEq] at ht
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := ht
    exact front_installs pid w u none ambient middle history hi hf (by simp)
  | some ctx =>
    exact (front_installs pid w u (some ctx) ambient middle history hi hf (by
      intro c hc; cases hc
      exact front_configured pid ctx w u v ambient middle ambient' result configured hf ht)).retain
        (Origins.tail_retains pid ctx.slot middle ambient' ht)

/-- Normal support for the unchanged once-only session observer. The incoming
receipt history is supplied and valid; lifetime projection keeps its existing
separate AllocationInv premise. Failed tails retain the old observer's exact
journal, with no configured endpoint asserted. -/
theorem observed_support (pid : PeerId) (w v : WGWorld) (result : Bool)
    (ambient ambient' : Ambient) (h t : List (MaterialOrigin.Event SessionOrigin.Receipt))
    (valid : MaterialOrigin.Valid SessionOrigin.Receipt.Valid h)
    (configured : ConfiguredIdentity.Inv w) (hi : Inv (h.filterMap Origins.receipt?) w)
    (hr : runWGPrefix (SessionOrigin.observed pid) w ambient h = (.ok ((result,v),ambient'),t)) :
    Inv (t.filterMap Origins.receipt?) v := by
  obtain ⟨suffix,hs,truth,normal⟩ := SessionOrigin.observedFront_valid pid w ambient h valid
  change (runStatePrefix (SessionOrigin.observedFront pid) w ambient h).2 = h ++ suffix at hs
  change runStatePrefix (SessionOrigin.observed pid) w ambient h = _ at hr
  unfold SessionOrigin.observed at hr
  rw [runStatePrefix_bind] at hr
  have hc := runWGPrefix_receiptWGObserved (SessionOrigin.observedFront pid)
    (MaterialOrigin.Event.receipt ∘ SessionOrigin.Receipt.material pid) w ambient h
  simp only [runWGPrefix] at hc
  rw [hc] at hr
  cases hf : runStatePrefix (SessionOrigin.observedFront pid) w ambient h with
  | mk output middleHistory =>
    simp only [hf] at hs
    cases output with
    | error e => simp [hf] at hr
    | ok output =>
      rcases output with ⟨⟨front,u⟩,middle⟩
      simp only [hf,Function.comp_apply] at hr
      have source : ((SessionOrigin.front pid).run w).run ambient = .ok ((front,u),middle) :=
        (SessionOrigin.observedFront_erases pid w ambient h).symm.trans (congrArg Prod.fst hf)
      have incl : ∀ r ∈ (h.filterMap Origins.receipt? ++
          [SessionOrigin.Receipt.material pid ⟨front,w,u,ambient,middle⟩]),
          r ∈ (middleHistory ++ [MaterialOrigin.Event.receipt
            (SessionOrigin.Receipt.material pid ⟨front,w,u,ambient,middle⟩)]).filterMap Origins.receipt? := by
        intro r hm
        rw [hs]
        simpa only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,Origins.receipt?,List.append_assoc]
          using (show r ∈ h.filterMap Origins.receipt? ++ suffix.filterMap Origins.receipt? ++
            [SessionOrigin.Receipt.material pid ⟨front,w,u,ambient,middle⟩] from by
              rcases List.mem_append.mp hm with hm | hm
              · exact List.mem_append_left _ (List.mem_append_left _ hm)
              · exact List.mem_append_right _ hm)
      cases front with
      | none =>
        simp only [runStatePrefix_pure,Prod.mk.injEq,Except.ok.injEq] at hr
        obtain ⟨⟨⟨rfl,rfl⟩,rfl⟩,rfl⟩ := hr
        exact (front_installs pid w u none ambient middle _ hi source (by simp)).mono incl
      | some ctx =>
        change runWGPrefix (Origins.accessNative (SessionOrigin.tailPrefix pid ctx.slot)) u middle
          (middleHistory ++ [MaterialOrigin.Event.receipt
            (SessionOrigin.Receipt.material pid ⟨some ctx,w,u,ambient,middle⟩)]) =
              (.ok ((result,v),ambient'),t) at hr
        have tail : ((SessionOrigin.tail pid ctx.slot).run u).run middle = .ok ((result,v),ambient') :=
          (focusStatePrefix_erases _ _ (SessionOrigin.tail_erases pid ctx.slot) u middle _).symm.trans
            (congrArg Prod.fst hr)
        have frame := Origins.access_receipts (R := SessionOrigin.Receipt)
          ((SessionOrigin.tailPrefix pid ctx.slot).run u) middle
          (middleHistory ++ [MaterialOrigin.Event.receipt
            (SessionOrigin.Receipt.material pid ⟨some ctx,w,u,ambient,middle⟩)])
        change (runWGPrefix (Origins.accessNative (SessionOrigin.tailPrefix pid ctx.slot)) u middle
          (middleHistory ++ [MaterialOrigin.Event.receipt
            (SessionOrigin.Receipt.material pid ⟨some ctx,w,u,ambient,middle⟩)])).2.filterMap Origins.receipt? =
              (middleHistory ++ [MaterialOrigin.Event.receipt
                (SessionOrigin.Receipt.material pid ⟨some ctx,w,u,ambient,middle⟩)]).filterMap Origins.receipt? at frame
        rw [hr] at frame
        rw [frame]
        exact ((front_installs pid w u (some ctx) ambient middle _ hi source (by
          intro c hc; cases hc
          exact front_configured pid ctx w u v ambient middle ambient' result configured source tail)).retain
            (Origins.tail_retains pid ctx.slot middle ambient' tail)).mono incl

/-- The peer is fixed by the actual non-NULL key owner, while every origin
field still belongs to the same supporting receipt. -/
def ByPeer (history : List SessionOrigin.Receipt) (epoch slot : Nat) (key : Keypair) (pid : PeerId) : Prop :=
  ∃(run : WGRunWitness (Option SessionOrigin.Context)) (ctx : SessionOrigin.Context) (d : Device) (original : Keypair),
    SessionOrigin.Receipt.material pid run∈history ∧ run.Valid (SessionOrigin.front pid) ∧
    run.value=some ctx ∧ ctx.slot=slot ∧ Configured pid run.before ctx ∧
    run.after.dev=some d ∧ d.ifindex=epoch ∧ d.keypairs[slot]?=some original ∧
    original.receiving.isValid=true ∧ original.peer=ctx.word ∧ material key=material original ∧
    ctx.word=some pid

theorem Supported.byPeer (h : Supported xs epoch slot key) (word : key.peer=some pid) :
    ByPeer xs epoch slot key pid := by
  obtain ⟨q,r,ctx,d,k,hm,hr,hv,hs,hc,hd,he,hk,valid,hw,mat,keep⟩:=h
  have actual : ctx.word=some pid := Origins.WordLe.some (word ▸ keep)
  have self : ctx.word=some q := hc.choose_spec.2.2.2.2
  have eq : q=pid := Option.some.inj (self.symm.trans actual)
  subst q
  exact ⟨r,ctx,d,k,hm,hr,hv,hs,hc,hd,he,hk,valid,hw,mat,actual⟩

end Leanux.Proofs.WG.ConfiguredSession
