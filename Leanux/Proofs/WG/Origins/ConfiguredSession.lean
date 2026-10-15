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
  intro w result v hr
  cases result with
  | none => exact congrArg (fun k:Kernel=>k.wg.map ConfiguredIdentity.state) (Origins.create_none _ _ _ hr)
  | some id =>
    obtain ⟨d,hd,hid,hv⟩:=Origins.create_some _ _ _ _ hr
    simp [ConfiguredIdentity.view,hv,keyAllocationWorld,keyAllocationDevice,hd,ConfiguredIdentity.state]

theorem derive_view (id : KeypairId) (initiator : Bool) (ck : List UInt8) :
    SameView ConfiguredIdentity.view (deriveKeys id initiator ck) := by
  intro w x v hr; cases x
  obtain ⟨d,old,key,hd,hk,hv,rest⟩:=Origins.derive_effect _ _ _ _ _ hr
  simp [ConfiguredIdentity.view,hv,hd,ConfiguredIdentity.state]

theorem init_view (id : KeypairId) (b : Bool) (remote : Nat) :
    SameView ConfiguredIdentity.view (SessionOrigin.initKey id b remote) := by
  apply SameView.of_wp; intro s
  have hg:=(ConfiguredIdentity.getKeypair_view id).wp (fun t=>t=s)
  have hs:=fun k=>(ConfiguredIdentity.setKeypair_view id k).wp (fun t=>t=s)
  mvcgen [SessionOrigin.initKey,hg,hs]

theorem front_view (pid : PeerId) : SameView ConfiguredIdentity.view (SessionOrigin.front pid) := by
  apply SameView.of_wp; intro s
  have hg:=ConfiguredIdentity.getPeer_spec (fun t=>t=s) pid
  have hw:=(ConfiguredIdentity.kernel (indexOwner_peerWord_sameKernel (.handshake pid))).wp (fun t=>t=s)
  have hc:=fun wd=>(create_view wd).wp (fun t=>t=s)
  have hi:=fun id b remote=>(init_view id b remote).wp (fun t=>t=s)
  have hd:=fun id b ck=>(derive_view id b ck).wp (fun t=>t=s)
  have hr:=fun st=>(ConfiguredIdentity.kernel (sessionStateRejected_sameKernel st)).wp (fun t=>t=s)
  mvcgen [SessionOrigin.front,SessionOrigin.frontWith,hg,hw,hc,hi,hd,hr,branch,invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [ConfiguredIdentity.view]

theorem replace_view (pid kp : Nat) : SameView ConfiguredIdentity.view (indexReplaceHandshake pid kp) := by
  apply SameView.of_wp; intro s
  have hm:=ConfiguredIdentity.modifyDev_spec (fun t=>t=s)
  mvcgen [indexReplaceHandshake,indexHashed,getDev,getK,invariant,branch,hm]
  all_goals intro d; rfl

theorem tail_view (pid kp : Nat) : SameView ConfiguredIdentity.view (SessionOrigin.tail pid kp) := by
  apply SameView.of_wp; intro s
  have hg:=ConfiguredIdentity.getPeer_spec (fun t=>t=s) pid
  have hz:=(ConfiguredIdentity.handshakeZero_view pid).wp (fun t=>t=s)
  have ha:=(ConfiguredIdentity.addNewKeypair_view pid kp).wp (fun t=>t=s)
  have hd:=(ConfiguredIdentity.kernel (indexOwner_peerDeref_sameKernel (.handshake pid))).wp (fun t=>t=s)
  have hi:=(replace_view pid kp).wp (fun t=>t=s)
  mvcgen [SessionOrigin.tail,SessionOrigin.tailWith,hg,hz,ha,hd,hi,branch,unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [ConfiguredIdentity.view]

/-- Actual non-NULL dereference, preserving the entry configured view. -/
theorem deref_spec (pid : PeerId) (P : Option ConfiguredIdentity.State→Prop) :
    ⦃fun w=>⌜P (ConfiguredIdentity.view w)⌝⦄ IndexOwner.peerDeref (.handshake pid)
    ⦃⇓? result w=>⌜P (ConfiguredIdentity.view w) ∧ ∃s p,ConfiguredIdentity.view w=some s ∧ s.peers pid=some p ∧ p.word=some result⌝⦄ := by
  have hg:=ConfiguredIdentity.getPeer_spec P pid
  mvcgen [IndexOwner.peerDeref,IndexOwner.peerWord,hg,unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [ConfiguredIdentity.cell,Option.bind_eq_some_iff]
  rename_i hpre hpost he
  obtain ⟨_,s,hs,hp⟩ := hpost
  exact ⟨s,hs,_,hp,rfl⟩

/-- A normal tail really passed the live-peer test and non-NULL handshake
owner dereference; neither is inferred merely from a Some front receipt. -/
theorem tail_live (pid kp : Nat) (w v : World) (result : Bool)
    (hr : (SessionOrigin.tail pid kp).run w=.ok (result,v)) :
    ∃s p,ConfiguredIdentity.view w=some s ∧ s.peers pid=some p ∧ p.dead=false ∧ p.word.isSome=true := by
  unfold SessionOrigin.tail SessionOrigin.tailWith at hr
  rw [bind_ok] at hr
  obtain ⟨z,a,hzero,hr⟩:=hr; cases z
  rw [bind_ok] at hr
  obtain ⟨p,b,hget,hr⟩:=hr
  obtain ⟨hba,dev,hdev,hp⟩:=Origins.getPeer_return _ _ _ _ hget
  subst b
  rw [bind_ok] at hr
  obtain ⟨alive,c,hbranch,hr⟩:=hr
  have hb : alive= !p.isDead ∧ c=CounterWindow.record a .sessionAlive (!p.isDead) := by
    simpa [CounterWindow.branch_run,eq_comm] using hbranch
  obtain ⟨rfl,rfl⟩:=hb
  cases dead:p.isDead with
  | true => simp [dead,unsupported] at hr
  | false =>
    simp only [dead,Bool.not_false,↓reduceIte,bind_ok] at hr
    obtain ⟨z,d,hrotate,q,e,hderef,rest⟩:=hr; cases z
    have hv : ConfiguredIdentity.view d=ConfiguredIdentity.view w :=
      (ConfiguredIdentity.addNewKeypair_view pid kp _ _ d hrotate).trans
        (ConfiguredIdentity.handshakeZero_view pid w () a hzero)
    have facts:=(hoare_iff_triple _ _ _).mpr
      (deref_spec pid (fun t=>t=ConfiguredIdentity.view w)) d q e hv hderef
    obtain ⟨he,s,x,hs,hx,hword⟩:=facts
    have hw : ConfiguredIdentity.view w=some (ConfiguredIdentity.state dev) :=
      (ConfiguredIdentity.handshakeZero_view pid w () a hzero).symm.trans (by simp [ConfiguredIdentity.view,hdev])
    have es : s=ConfiguredIdentity.state dev := Option.some.inj (hs.symm.trans (he.trans hw))
    subst s
    have ex : x=ConfiguredIdentity.cell p := Option.some.inj
      (hx.symm.trans (by simp [ConfiguredIdentity.state,hp]))
    subst x
    exact ⟨ConfiguredIdentity.state dev,ConfiguredIdentity.cell p,hw,by simp [ConfiguredIdentity.state,hp],dead,by simp [hword]⟩

/-- The same full peer record at this actual front's entry supplies the table
row, allocation stamp and configured static key. Later raw-slot identity is a
separate obligation. -/
def Configured (pid : PeerId) (w : World) (ctx : SessionOrigin.Context) : Prop :=
  ∃d,w.k.wg=some d ∧ d.peers[pid]?=some ctx.peer ∧
    (ctx.peer.remoteStatic,pid)∈d.peerHashtable ∧ ctx.peer.isDead=false ∧ ctx.word=some pid

theorem front_configured (pid : PeerId) (ctx : SessionOrigin.Context) (w u v : World)
    (result : Bool) (hi : ConfiguredIdentity.Inv w)
    (hf : (SessionOrigin.front pid).run w=.ok (some ctx,u))
    (ht : (SessionOrigin.tail pid ctx.slot).run u=.ok (result,v)) : Configured pid w ctx := by
  obtain ⟨d,key,hd,hp,hst,hw,hslot,rest⟩:=Origins.front_effect pid ctx w u hf
  obtain ⟨s,p,hs,hcell,alive,nonnull⟩:=tail_live pid ctx.slot u v result ht
  have hview : ConfiguredIdentity.view w=some (ConfiguredIdentity.state d) := by simp [ConfiguredIdentity.view,hd]
  have eqs : s=ConfiguredIdentity.state d := Option.some.inj
    (hs.symm.trans ((front_view pid w _ u hf).trans hview))
  subst s
  have eqp : p=ConfiguredIdentity.cell ctx.peer := Option.some.inj
    (hcell.symm.trans (by simp [ConfiguredIdentity.state,hp]))
  subst p
  have inv:=hi _ hview
  have self:=inv.self pid (ConfiguredIdentity.cell ctx.peer) (by simp [ConfiguredIdentity.state,hp])
  have word : ctx.word=some pid := by
    rcases self with h|h
    · change ctx.peer.handshakeEntryPeer=none at h
      change ctx.peer.handshakeEntryPeer.isSome=true at nonnull
      simp [h] at nonnull
    · exact hw.trans h
  exact ⟨d,hd,hp,inv.live _ _ (by simp [ConfiguredIdentity.state,hp]) alive (by simp),alive,word⟩

/-- Material, owner and configured identity use one receipt and one Context. -/
def Supported (history : List SessionOrigin.Receipt) (epoch : Nat) (slot : KeypairId) (key : Keypair) : Prop :=
  ∃ (pid : PeerId) (run : RunWitness (Option SessionOrigin.Context))
    (ctx : SessionOrigin.Context) (d : Device) (original : Keypair),
    SessionOrigin.Receipt.material pid run∈history ∧ run.Valid (SessionOrigin.front pid) ∧
    run.value=some ctx ∧ ctx.slot=slot ∧ Configured pid run.before ctx ∧
    run.after.k.wg=some d ∧ d.ifindex=epoch ∧ d.keypairs[slot]?=some original ∧
    original.receiving.isValid=true ∧ original.peer=ctx.word ∧
    material key=material original ∧ Origins.WordLe key.peer ctx.word

def Inv (history : List SessionOrigin.Receipt) (w : World) : Prop :=
  ∀d,w.k.wg=some d → ∀id key,d.keypairs[id]?=some key → key.receiving.isValid=true →
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

theorem front_installs (pid : PeerId) (w u : World) (result : Option SessionOrigin.Context)
    (history : List SessionOrigin.Receipt) (hi : Inv history w)
    (hr : (SessionOrigin.front pid).run w=.ok (result,u))
    (configured : ∀ctx,result=some ctx → Configured pid w ctx) :
    Inv (history++[SessionOrigin.Receipt.material pid ⟨result,w,u⟩]) u := by
  cases result with
  | none =>
    have hk:=Origins.front_none pid w u hr
    intro d hd id k hkey valid
    exact (hi d (by simpa [hk] using hd) id k hkey valid).mono (fun r h=>List.mem_append_left _ h)
  | some ctx =>
    obtain ⟨d,key,hd,hp,hs,hw,hslot,hview,hstamp,hword,hvalid⟩:=Origins.front_effect _ _ _ _ hr
    intro dev hdev id k hk valid
    have fields : (dev.ifindex,fun q=>dev.keypairs[q]?)=
        (d.ifindex,fun q=>if ctx.slot=q then some key else d.keypairs[q]?) := by
      simpa [Origins.view,hdev] using hview
    have epoch : dev.ifindex=d.ifindex := congrArg Prod.fst fields
    have keys:=congrFun (congrArg Prod.snd fields) id
    dsimp only at keys
    by_cases he:ctx.slot=id
    · subst id
      have ek : k=key := by rw [hk] at keys; simpa using keys
      subst k
      exact ⟨pid,⟨some ctx,w,u⟩,ctx,dev,key,by simp,hr,rfl,rfl,configured ctx rfl,
        hdev,rfl,hk,hvalid,hword,rfl,Or.inr hword⟩
    · have old : d.keypairs[id]?=some k := by simpa [he,hk] using keys.symm
      simpa only [epoch] using (hi d hd id k old valid).mono (fun r h=>List.mem_append_left _ h)

/-- Whole normal source decomposition. A stopped tail has no endpoint support
claim, although the unchanged lower observer retains its front receipt. -/
theorem beginSession_support (pid : PeerId) (w v : World) (result : Bool)
    (history : List SessionOrigin.Receipt) (configured : ConfiguredIdentity.Inv w)
    (hi : Inv history w) (hr : (beginSession pid).run w=.ok (result,v)) :
    ∃front u,(SessionOrigin.front pid).run w=.ok (front,u) ∧
      Inv (history++[SessionOrigin.Receipt.material pid ⟨front,w,u⟩]) v := by
  rw [SessionOrigin.factor,bind_ok] at hr
  obtain ⟨front,u,hf,ht⟩:=hr
  refine ⟨front,u,hf,?_⟩
  cases front with
  | none =>
    simp only [StateT.run_pure,Except.ok.injEq,Prod.mk.injEq] at ht
    obtain ⟨rfl,rfl⟩:=ht
    exact front_installs pid w v none history hi hf (by simp)
  | some ctx =>
    exact (front_installs pid w u (some ctx) history hi hf (by
      intro c hc; cases hc
      exact front_configured pid ctx w u v result configured hf ht)).retain (Origins.tail_retains pid ctx.slot ht)

/-- Normal support for the unchanged once-only session observer. The incoming
receipt history is supplied and valid; lifetime projection keeps its existing
separate AllocationInv premise. Failed tails retain the old observer's exact
journal, with no configured endpoint asserted. -/
theorem observed_support (pid : PeerId) (w v : World) (result : Bool)
    (h t : List (MaterialOrigin.Event SessionOrigin.Receipt))
    (valid : MaterialOrigin.Valid SessionOrigin.Receipt.Valid h)
    (configured : ConfiguredIdentity.Inv w) (hi : Inv (h.filterMap Origins.receipt?) w)
    (hr : runPrefix (SessionOrigin.observed pid) w h=(.ok (result,v),t)) :
    Inv (t.filterMap Origins.receipt?) v := by
  obtain ⟨suffix,hs,truth,normal⟩:=SessionOrigin.observedFront_valid pid w h valid
  unfold SessionOrigin.observed at hr
  rw [runPrefix_bind,runPrefix_receiptObserved] at hr
  cases hf : runPrefix (SessionOrigin.observedFront pid) w h with
  | mk output middle =>
    simp only [hf] at hs
    cases output with
    | error e => simp [hf] at hr
    | ok output =>
      rcases output with ⟨front,u⟩
      simp only [hf,Function.comp_apply] at hr
      have source : (SessionOrigin.front pid).run w=.ok (front,u) :=
        (SessionOrigin.observedFront_erases pid w h).symm.trans (congrArg Prod.fst hf)
      have incl : ∀r∈(h.filterMap Origins.receipt? ++ [SessionOrigin.Receipt.material pid ⟨front,w,u⟩]),
          r∈(middle++[MaterialOrigin.Event.receipt (SessionOrigin.Receipt.material pid ⟨front,w,u⟩)]).filterMap Origins.receipt? := by
        intro r hm
        rw [hs]
        simpa only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,Origins.receipt?,List.append_assoc]
          using (show r∈h.filterMap Origins.receipt? ++ suffix.filterMap Origins.receipt? ++ [SessionOrigin.Receipt.material pid ⟨front,w,u⟩] from by
            rcases List.mem_append.mp hm with hm|hm
            · exact List.mem_append_left _ (List.mem_append_left _ hm)
            · exact List.mem_append_right _ hm)
      cases front with
      | none =>
        simp only [hf,runPrefix_pure,Prod.mk.injEq,Except.ok.injEq] at hr
        obtain ⟨⟨rfl,rfl⟩,rfl⟩:=hr
        exact (front_installs pid w u none _ hi source (by simp)).mono incl
      | some ctx =>
        change runPrefix (MaterialOrigin.access (SessionOrigin.tailPrefix pid ctx.slot)) u
          (middle++[MaterialOrigin.Event.receipt (SessionOrigin.Receipt.material pid ⟨some ctx,w,u⟩)])=(.ok (result,v),t) at hr
        have tail : (SessionOrigin.tail pid ctx.slot).run u=.ok (result,v) :=
          (MaterialOrigin.access_erases (SessionOrigin.tail_erases pid ctx.slot) u _).symm.trans (congrArg Prod.fst hr)
        have frame:=Origins.access_receipts (R:=SessionOrigin.Receipt) (SessionOrigin.tailPrefix pid ctx.slot) u
          (middle++[MaterialOrigin.Event.receipt (SessionOrigin.Receipt.material pid ⟨some ctx,w,u⟩)])
        rw [hr] at frame
        rw [frame]
        exact ((front_installs pid w u (some ctx) _ hi source (by
          intro c hc; cases hc
          exact front_configured pid ctx w u v result configured source tail)).retain
          (Origins.tail_retains pid ctx.slot tail)).mono incl

/-- The peer is fixed by the actual non-NULL key owner, while every origin
field still belongs to the same supporting receipt. -/
def ByPeer (history : List SessionOrigin.Receipt) (epoch slot : Nat) (key : Keypair) (pid : PeerId) : Prop :=
  ∃(run : RunWitness (Option SessionOrigin.Context)) (ctx : SessionOrigin.Context) (d : Device) (original : Keypair),
    SessionOrigin.Receipt.material pid run∈history ∧ run.Valid (SessionOrigin.front pid) ∧
    run.value=some ctx ∧ ctx.slot=slot ∧ Configured pid run.before ctx ∧
    run.after.k.wg=some d ∧ d.ifindex=epoch ∧ d.keypairs[slot]?=some original ∧
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
