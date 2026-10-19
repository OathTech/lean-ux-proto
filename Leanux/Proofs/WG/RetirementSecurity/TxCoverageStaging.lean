import Leanux.Proofs.WG.RetirementSecurity.TxCoverageCreate
import Leanux.Proofs.WG.RetirementSecurity.TxCryptStagingFrames

/-! Full native staged-send coverage. Key refusal restores plaintext before
any allocation; successful allocation transfers every new cell to createData.
The coverage carrier needs no allocation frontier or incoming key-credit
premise. Uniqueness is supplied independently by TxInventory. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Std.Do
open Queues.RxCredits

theorem coverage_passive {action : WG.M α} (wire : SameView txCryptWire action)
    (queues : SameView handoffTxView action) : Preserves (TxCoverage locals) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact before.cells
    (congrArg Prod.snd ((ProjectedAction.iff_run_ambient _ _ _).mp wire w a result v b run))
    (queueContents_of_exact ((ProjectedAction.iff_run_ambient _ _ _).mp queues w a result v b run))

theorem coverage_key_get (kid : Option KeypairId) : Preserves (TxCoverage locals) (keypairGet kid) :=
  coverage_passive (keyGet_cryptWire kid) (keyGet_tx_queues kid)

theorem coverage_no_key (pid : PeerId) (packets : List WG.Packet) (kid : Option KeypairId)
    (invalid : Bool) : Preserves (TxCoverage locals) (stagedOutNokey pid packets kid invalid) :=
  coverage_passive (noKey_cryptWire pid packets kid invalid) (noKey_tx_queues pid packets kid invalid)

theorem coverage_set_key (kid : KeypairId) (key : Keypair) :
    Preserves (TxCoverage locals) (setKeypair kid key) := by
  apply coverage_passive
  · intro initial
    change Preserves (fun w=>txCryptWire w=initial) _
    unfold setKeypair
    repeat' crypt_wire_step initial
  · intro initial
    change Preserves (fun w=>handoffTxView w=initial) _
    unfold setKeypair
    repeat' crypt_queue_step initial

theorem TxCoverage.staged_submit (before : TxCoverage locals w) (pid kid : Nat)
    (packets : List DataPacket) (a b : Ambient)
    (run : ((stagedSubmit pid kid packets).run w).run a=.ok (((),v),b)) : TxCoverage locals v := by
  simp only [stagedSubmit,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨_,u,c,acquireRun,tail⟩:=run
  have frame : SameView ownershipPointView (Affiliation.sendAcquire kid) := by
    intro initial
    change Preserves (fun w=>ownershipPointView w=initial) _
    unfold Affiliation.sendAcquire
    repeat' first
      | (rx_retention_head peerGet; exact (peerGet_ownership _).wp (·=initial))
      | ownership_source_step initial
  exact (before.points ((ProjectedAction.iff_run_ambient _ _ _).mp frame w a () u c acquireRun)).allocate_create
    pid packets c b (by simpa only [MaterialOrigin.bind_ok_ambient] using tail)

theorem coverage_staged_key (locals : List TxLocalBatch) (pid kid : Nat) (packets : List WG.Packet) :
    Preserves (TxCoverage locals) (stagedKeySource pid kid packets) := by
  let P := TxCoverage locals
  have getter : Preserves P (getKeypair kid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a k v b before run
    exact (KeyTimes.getKeypair_return kid w v k a b run).1 ▸ before
  have setter := coverage_set_key (locals:=locals)
  have expired := fun date=>(branchExpired_sameWGWorld .stagedBirthdateExpired date REJECT_AFTER_TIME).wp P
  have ecn := fun pkt=>(ipTunnelEcnEncap_sameWGWorld pkt).wp P
  have out := coverage_no_key (locals:=locals) pid packets (some kid)
  have submit (data : List DataPacket) : Preserves P (stagedSubmit pid kid data) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b before run
    cases result
    exact before.staged_submit pid kid data a b run
  unfold stagedKeySource
  change Preserves P _
  simp (config := {zeta := false}) only [branch,branchCmp]
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head getKeypair; exact getter)
    | (index_material_head setKeypair; exact setter _ _)
    | (index_material_head branchExpired; exact expired _)
    | (index_material_head ipTunnelEcnEncap; exact ecn _)
    | (index_material_head stagedOutNokey; exact out _)
    | (index_material_head stagedSubmit; exact submit _)
    | (index_material_head ForIn.forIn; apply list_view_spec id P)
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | material_component
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match

theorem TxCoverage.staged (before : TxCoverage locals w) (pid : PeerId) (a b : Ambient)
    (run : ((sendStagedPackets pid).run w).run a=.ok (((),v),b)) : TxCoverage locals v := by
  rw [←stagedFullSource_eq] at run
  simp only [stagedFullSource,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,u,c,readRun,empty,t,e,branchRun,tail⟩:=run
  obtain ⟨same,clock,d,device,stored⟩:=Origins.getPeer_return pid w u p a c readRun
  subst u
  subst c
  have same : t=w := by cases branchRun; rfl
  subst t
  cases empty with
  | true => simp only [ite_true] at tail; cases tail; exact before
  | false =>
    simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨_,u,c,setRun,kp,t,f,getRun,missing,s,g,branchRun,tail⟩:=tail
    have after : u=replacePeer w d pid {p with staged:=[]} := by
      have equal : replacePeer w d pid {p with staged:=[]}=u ∧ e=c := by
        simpa [setPeer,modifyDev,replacePeer,device] using setRun
      exact equal.1.symm
    have kept : TxCoverage locals u := after ▸ before.exchange device stored _ (List.Perm.refl _)
    have acquired := (hoare_iff_run_ambient _ _ _).mp (coverage_key_get p.keypairCurrent)
      u c kp t f kept getRun
    have same : s=t := by cases branchRun; rfl
    subst s
    cases missing with
    | true =>
      simp only [ite_true] at tail
      exact (hoare_iff_run_ambient _ _ _).mp (coverage_no_key pid p.staged kp false)
        t g () v b acquired tail
    | false =>
      simp only [Bool.false_eq_true,ite_false] at tail
      cases kp with
      | none => cases tail
      | some kid =>
        exact (hoare_iff_run_ambient _ _ _).mp (coverage_staged_key locals pid kid p.staged)
          t g () v b acquired tail

end Leanux.Proofs.WG.RetirementSecurity
