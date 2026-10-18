import Leanux.Proofs.WG.Config.BranchSource
import Leanux.Proofs.WG.Packets.AffiliationCuts
import Leanux.Proofs.WG.Queues.RxPollPrimitives

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.DataIngressRules
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing
open Lifetimes Queues

def Acquired (P : WGWorld → Prop) (H : KeypairId → PeerId → WGWorld → Prop)
    (K : Option PeerId → WGWorld → Prop) (pair : Option KeypairId × Option PeerId) (w : WGWorld) : Prop :=
  P w ∧ (pair.1=none → K pair.2 w) ∧
    ∀ kid pid,pair=(some kid,some pid) → H kid pid w

theorem preserves (P : WGWorld → Prop) (H : KeypairId → PeerId → WGWorld → Prop)
    (K : Option PeerId → WGWorld → Prop) (msg : List UInt8) (src : SkbSource) (ds : Nat)
    (front : Hoare (do let entry ← indexLookup [.keypair] (u32le msg 4); Affiliation.receiveKeyAcquire entry)
      P (Acquired P H K))
    (held_safe : ∀ kid pid w,H kid pid w → P w)
    (keyPut : ∀ kid pid, Hoare (keypairPut (some kid) false) (H kid pid) (fun _ => K (some pid)))
    (peerPut : ∀ peer, Hoare (WG.peerPut peer) (K peer) (fun _ => P))
    (newRx : ∀ kid pid,Preserves (H kid pid) (newRxSkb {peer:=pid,keypair:=kid,bytes:=msg,source:=src,ds}))
    (enqueue : ∀ kid pid id,Preserves (H kid pid) (enqueuePerDeviceAndPeerRx id))
    (publish : ∀ kid pid id,Preserves (H kid pid) (enqueuePerPeerRx (pure () : WG.M Unit) id .dead))
    (free : ∀ id,Preserves P (freeRxSkb id)) :
    Preserves P (consumeData msg src ds) := by
  have hbranch (Q : WGWorld → Prop) (site : Decision) (value : Bool) :
      Hoare (Leanux.branch site value) Q (fun result w=>result=value ∧ Q w) :=
    Config.branch_state_spec Q site value
  have read (Q : WGWorld → Prop) (pid : PeerId) : Preserves Q (getPeer pid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a p v b pre run
    exact (getPeer_normal pid w v p a b run).1 ▸ pre
  have finish (kid : KeypairId) (pid : PeerId) (id : SkbId) (ret : Int) :
      Hoare (do
        if ← Leanux.branch .dataEpipe (ret == -EPIPE) then enqueuePerPeerRx (pure () : WG.M Unit) id .dead
        if ← WG.orM (Leanux.branch .dataEnqueueOk (ret==0)) (Leanux.branch .dataEnqueueOkEpipe (ret == -EPIPE)) then return
        keypairPut (some kid) false
        WG.peerPut (some pid)
        freeRxSkb id) (H kid pid) (fun _=>P) := by
    have suffix : Hoare (do
        if ← WG.orM (Leanux.branch .dataEnqueueOk (ret==0)) (Leanux.branch .dataEnqueueOkEpipe (ret == -EPIPE)) then return
        keypairPut (some kid) false
        WG.peerPut (some pid)
        freeRxSkb id) (H kid pid) (fun _=>P) := by
      have test : Preserves (H kid pid)
          (WG.orM (Leanux.branch .dataEnqueueOk (ret==0)) (Leanux.branch .dataEnqueueOkEpipe (ret == -EPIPE))) := by
        unfold WG.orM
        apply preserves_bind (hoare_liftAmbient (AmbientM.branch .dataEnqueueOk (ret==0)) (H kid pid))
        intro ok
        cases ok with
        | false => exact hoare_liftAmbient (AmbientM.branch .dataEnqueueOkEpipe (ret == -EPIPE)) (H kid pid)
        | true => exact preserves_pure true
      apply hoare_bind _ _ test
      intro done
      cases done with
      | true =>
        apply hoare_consequence (preserves_pure () : Preserves P (pure () : WG.M Unit))
        · exact held_safe kid pid
        · exact fun _ _ h=>h
      | false =>
        simp only [Bool.false_eq_true,ite_false]
        exact hoare_bind _ _ (keyPut kid pid) (fun _=>
          hoare_bind _ _ (peerPut (some pid)) (fun _=>free id))
    apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .dataEpipe (ret == -EPIPE)) (H kid pid))
    intro pipe
    cases pipe with
    | false => exact suffix
    | true => exact hoare_bind _ _ (publish kid pid id) (fun _=>suffix)
  rw [←Affiliation.consumeDataSource_eq]
  unfold Affiliation.consumeDataSource
  rw [←bind_assoc]
  apply hoare_bind _ _ front
  intro pair
  rcases pair with ⟨kp,peer⟩
  apply hoare_bind _ _ (hbranch (Acquired P H K (kp,peer)) .dataNoKeypair kp.isNone)
  intro absent
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  rcases pre with ⟨rfl,pre⟩
  cases kp with
  | none =>
    have clean := hoare_bind _ _ (peerPut peer) (fun _=>preserves_pure ())
    exact (hoare_iff_run_ambient _ _ _).mp clean w a result v b (pre.2.1 rfl) run
  | some kid =>
    cases peer with
    | none => simp [invariant,AmbientM.invariant] at run; cases run
    | some pid =>
      have hp : H kid pid w := pre.2.2 kid pid rfl
      have body : Hoare (do
          if ← Leanux.branch .dataPeerDead (←getPeer pid).isDead then
            keypairPut (some kid) false
            WG.peerPut (some pid)
            return
          let id ← newRxSkb {peer:=pid,keypair:=kid,bytes:=msg,source:=src,ds}
          let ret ← enqueuePerDeviceAndPeerRx id
          if ← Leanux.branch .dataEpipe (ret == -EPIPE) then enqueuePerPeerRx (pure () : WG.M Unit) id .dead
          if ← WG.orM (Leanux.branch .dataEnqueueOk (ret==0)) (Leanux.branch .dataEnqueueOkEpipe (ret == -EPIPE)) then return
          keypairPut (some kid) false
          WG.peerPut (some pid)
          freeRxSkb id) (H kid pid) (fun _=>P) := by
        apply hoare_bind _ _ (read (H kid pid) pid)
        intro p
        apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .dataPeerDead p.isDead) (H kid pid))
        intro dead
        cases dead with
        | true =>
          exact hoare_bind _ _ (keyPut kid pid) (fun _=>
            hoare_bind _ _ (peerPut (some pid)) (fun _=>preserves_pure ()))
        | false =>
          simp only [Bool.false_eq_true,ite_false]
          exact hoare_bind _ _ (newRx kid pid) (fun id=>
            hoare_bind _ _ (enqueue kid pid id) (finish kid pid id))
      exact (hoare_iff_run_ambient _ _ _).mp body w a result v b hp run

end Leanux.Proofs.WG.Index.DataIngressRules
