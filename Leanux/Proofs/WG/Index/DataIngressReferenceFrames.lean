import Leanux.Proofs.WG.Index.DataIngressReferenceModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.DataIngress
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits

theorem held_frame_at {α : Type} (P : WGWorld → Prop) (action : WG.M α)
    (safe : ∀d,Hoare action (fun w=>P w ∧ w.dev=some d) (fun _=>P))
    (frame : ∀d,Ensures action (referencesAt d) (fun _=>referencesAt d)) (kid : KeypairId) (pid : PeerId) :
    Preserves (Held P kid pid) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  obtain ⟨initial,d,p,k,device,peer,peerCount,key,keyCount⟩ := pre
  have after := (hoare_iff_run_ambient _ _ _).mp (safe d) w a result v b ⟨initial,device⟩ run
  have observed := frame d w a result v b (by simp [referencesAt,device]) run
  cases final : v.dev with
  | none => simp [referencesAt,final] at observed
  | some e =>
    have same : ownerReferences e=ownerReferences d := by simpa [referencesAt,final] using observed
    have keys : e.keypairs=d.keypairs := congrArg (fun x=>x.2.1) same
    have peers := congrFun (congrArg (fun x=>x.2.2) same) pid
    cases resident : e.peers[pid]? with
    | none => simp [ownerReferences,resident,peer] at peers
    | some q =>
      simp only [ownerReferences,resident,peer,Option.map_some,Option.some.injEq,Prod.mk.injEq] at peers
      exact ⟨after,e,q,k,final,resident,by omega,by simpa [keys] using key,keyCount⟩

theorem held_frame {α : Type} (P : WGWorld → Prop) (action : WG.M α)
    (safe : Preserves P action)
    (frame : ∀d,Ensures action (referencesAt d) (fun _=>referencesAt d)) (kid : KeypairId) (pid : PeerId) :
    Preserves (Held P kid pid) action :=
  held_frame_at P action (fun _=>hoare_consequence safe (fun _ h=>h.1) (fun _ _ h=>h)) frame kid pid

theorem coherent_frame {α : Type} (action : WG.M α)
    (frame : ∀d,Ensures action (referencesAt d) (fun _=>referencesAt d)) (d : Device) :
    Hoare action (fun w=>DeviceSafe HashedOwnersCoherent w ∧ w.dev=some d)
      (fun _=>DeviceSafe HashedOwnersCoherent) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  have observed := frame d w a result v b (by simp [referencesAt,pre.2]) run
  intro e ending
  have same : ownerReferences e=ownerReferences d := by simpa [referencesAt,ending] using observed
  exact ownerReferences_coherent d e same (pre.1 d pre.2)

theorem skb_coherent {α : Type} (action : SkbM α) :
    Preserves (DeviceSafe HashedOwnersCoherent) (liftSkb action) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  cases device : w.dev with
  | none => simp [liftSkb,getDev,device,invariant,AmbientM.invariant] at run; cases run
  | some d =>
    exact (hoare_iff_run_ambient _ _ _).mp
      (coherent_frame _ (fun d=>hoare_liftSkb_references_variant action d) d)
      w a result v b ⟨pre,device⟩ run

end Leanux.Proofs.WG.Index.DataIngress
