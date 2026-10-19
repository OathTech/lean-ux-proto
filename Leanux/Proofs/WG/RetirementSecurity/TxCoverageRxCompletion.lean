import Leanux.Proofs.WG.RetirementSecurity.TxCoverageHandshake

/-! Authenticated RX completion may stage waiting TX packets. Promotion,
endpoint updates and finishing receive keep existing TX coverage, while the
actual staged call accounts for every newly allocated TX cell. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxCoverageNative
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits
variable {locals : List TxLocalBatch}

def view (w : WGWorld) := (handoffTxView w,TxDisposition.txPackets w)

theorem view_frame (before : TxCoverage locals w) (same : view v=view w) : TxCoverage locals v :=
  before.cells (congrArg Prod.snd same) (queueContents_of_exact (congrArg Prod.fst same))

theorem geometry_frame {action : WG.M α} (geometry : SameView StagingOccurrences.geometry action)
    (queues : SameView handoffTxView action) : Preserves (TxCoverage locals) action :=
  contents (contents_factor queues) (geometry.factor Prod.snd)

theorem promote_send (before : TxCoverage locals w) (pid : PeerId) (kid : KeypairId) (a b : Ambient)
    (run : ((promoteAndSend pid kid).run w).run a=.ok (((),v),b)) : TxCoverage locals v := by
  simp only [promoteAndSend,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨fresh,u,c,confirmRun,flag,t,e,branchRun,tail⟩:=run
  have held := (hoare_iff_run_ambient _ _ _).mp
    (geometry_frame (confirmation_geometry pid kid)
      ((receivedWithKeypair_protect pid kid).factor (fun s=>s.2.2.1)))
    w a fresh u c before confirmRun
  have exactBranch : flag=fresh ∧ t=u := by cases branchRun; exact ⟨rfl,rfl⟩
  obtain ⟨sameFlag,sameWorld⟩:=exactBranch
  subst flag
  subst t
  cases fresh with
  | false => simp only [Bool.false_eq_true,ite_false] at tail; cases tail; exact held
  | true =>
    simp only [ite_true,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨_,t,f,timerRun,sendRun⟩:=tail
    have kept := (hoare_iff_run_ambient _ _ _).mp
      (maintenance (.handshakeComplete pid .walltimeLastHandshakeData)) u e () t f held timerRun
    exact kept.staged pid f b sendRun

theorem consume (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    Preserves (TxCoverage locals) (consumeDataDone pid pkt endpoint) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  rw [Packets.consumeDataDone_factor,rxPrepare_factor] at run
  simp only [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨ready,u,c,prepareRun,finishRun⟩:=run
  obtain ⟨_,t,e,endpointRun,_,s,f,promoteRun,restRun⟩:=prepareRun
  have held := (hoare_iff_run_ambient _ _ _).mp (maintenance (.endpoint pid endpoint))
    w a () t e before endpointRun
  have promoted := promote_send held pid pkt.keypair e f promoteRun
  have kept := (hoare_iff_run_ambient _ _ _).mp
    (wire (ownership_queues (prepareRest_ownership pid pkt)) (prepareRest_cryptWire pid pkt))
    s f ready u c promoted restRun
  cases ready with
  | none => cases finishRun; exact kept
  | some ready =>
    exact (hoare_iff_run_ambient _ _ _).mp
      (wire (ownership_queues (finishRx_ownership pid ready)) (finishRx_cryptWire pid ready))
      u c result v b kept finishRun

end Leanux.Proofs.WG.RetirementSecurity.TxCoverageNative
