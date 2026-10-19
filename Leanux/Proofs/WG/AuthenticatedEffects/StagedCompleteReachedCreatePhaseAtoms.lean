import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreatePhaseFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryReceiveFrames

/-! Concrete native frames for the original create atoms. Queue installation
is excluded: it consumes the unpublished alias and has its own phase rule. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePhase
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CreateDisposal CompleteCarrier StagedTerminalComplete Staged.Obligations
open HandshakeSecurity.StagedDisposal CreatePoints
set_option maxHeartbeats 600000

def Passive : Atom α → Prop
  | .queue _ _ _=>False
  | _=>True

theorem packet_view (id : SkbId) : SameView StagedEntry.view (getTxSkb id) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a packet v b performed
  exact congrArg StagedEntry.view (Packets.getTxSkb_current id w v packet a b performed).1

theorem choose_view (pid : PeerId) : SameView StagedEntry.view (cpumaskChooseOnline pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b performed
  cases hd : w.dev with
  | none=>
    simp [cpumaskChooseOnline,getPeer,getDev,hd,invariant,AmbientM.invariant] at performed
    cases performed
  | some d=>
    cases hp : d.peers[pid]? with
    | none=>
      simp [cpumaskChooseOnline,getPeer,getDev,hd,hp,invariant,AmbientM.invariant] at performed
      cases performed
    | some p=>
      by_cases invalid : 1 ≤ p.serialWorkCpu.getD 1 <;>
        simp [cpumaskChooseOnline,getPeer,getDev,setPeer,modifyDev,hd,hp,
          branch,AmbientM.branch,invalid,Nat.mod_one,List.foldlM] at performed
      all_goals rcases performed with ⟨⟨rfl,rfl⟩,rfl⟩
      · exact Queued.replace_peer hd hp rfl rfl rfl
      · rfl

theorem atom_normal (token : Atom α) (passive : Passive token)
    (before : Live rootLedger debts locals pid items h w.wg)
    (performed : runPrefix token.action w h=(.ok (value,v),last)) :
    Live rootLedger debts locals pid items last v.wg := by
  cases token with
  | fault α kind=>exact native_normal (show WG.M α from invariant kind.text) (fun initial=>hoare_liftAmbient (show AmbientM α from AmbientM.invariant kind.text) _) before performed
  | branch site flag=>exact native_normal _ (TimerFrames.branch_frame _ _) before performed
  | peer id=>exact access_normal _ _ (getPeerMixed_erases id) (Queued.read id) before performed
  | packet id=>exact access_normal _ _ (getTxSkbPrefix_erases id) (packet_view id) before performed
  | owner kid=>exact access_normal _ _ (peerDerefPrefix_erases _) (fun initial=>indexOwner_peerDeref_preserves _ _) before performed
  | acquire id=>exact access_normal _ _ (peerGetMixed_erases id) (Queued.acquire id) before performed
  | mark id state=>exact mark_normal id state before performed
  | queue=>exact passive.elim
  | device=>exact native_normal _ (TimerFrames.store getDev_sameWGStore) before performed
  | nextCpu cpu=>exact native_normal _ (TimerFrames.store (cpumaskNextOnlineFrom_sameStore cpu)) before performed
  | lastCpu cpu=>exact native_normal _ (ReceiveFrames.device (fun d=>{d with encryptLastCpu:=cpu}) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)) before performed
  | queueEncrypt=>exact native_normal _ (fun initial=>hoare_liftAmbient _ _) before performed
  | ring batch=>exact native_normal _ (ReceiveFrames.device (fun d=>{d with encryptQueue:=d.encryptQueue.produce batch}) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)) before performed
  | chooseCpu id=>exact access_normal _ _ (cpumaskChooseOnlinePrefix_erases id) (choose_view id) before performed
  | peekWork id=>exact native_normal _ (fun initial=>hoare_liftAmbient _ _) before performed
  | recordWork id=>exact native_normal _ (fun initial=>hoare_liftAmbient _ _) before performed
  | appendWork id=>exact native_normal _ (ReceiveFrames.device (fun d=>{d with txWorkQueue:=d.txWorkQueue++[id]}) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)) before performed
  | event event=>exact event_normal event before performed

theorem atom_covers (token : Atom α) (passive : Passive token)
    (before : Live rootLedger debts locals pid items h w.wg) :
    Covers (fun h w=>Live rootLedger debts locals pid items h w.wg) (.atom token) w h :=
  covers_atom token before (fun _ _ _ run=>atom_normal token passive before run)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePhase
