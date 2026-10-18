import Leanux.Proofs.WG.Index.DataIngressFrames
import Leanux.Proofs.WG.Index.DataIngressAcquireSource
import Leanux.Proofs.WG.Index.CryptPreparationSource
import Leanux.Proofs.WG.Index.TxDisposalCoreSource
import Leanux.Proofs.WG.Index.LookupRetirementClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.DataIngress
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits

theorem publish_core (id : SkbId) (state : PacketState) :
    Preserves Reached.Core (enqueuePerPeerRx (pure () : WG.M Unit) id state) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  cases result
  rw [publication_factor] at run
  simp only [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨pkt,x,ax,read,pid,y,ay,deref,u,z,az,acquire,u',mid,amid,middle,pay⟩ := run
  have xs := (Packets.getRxSkb_current id w x pkt a ax read).1
  have ys := (hoare_iff_run_ambient _ _ _).mp
    (indexOwner_peerDeref_preserves (.keypair pkt.keypair) (fun g=>g=x)) x ax pid y ay rfl deref
  have before : Reached.Core y := by simpa [ys,xs] using pre
  have credit := (hoare_iff_run_ambient _ _ _).mp (ConfigurationIndex.acquire_core pid) y ay u z az before acquire
  have safe := (hoare_iff_run_ambient _ _ _).mp (CryptCore.publication_middle_core pid id state)
    z az u' mid amid credit middle
  obtain ⟨d,p,device,resident,positive,effect⟩ := peerGet_loan pid y z ay az acquire
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp
    (publicationMiddle_frame pid id state) z az u' mid amid middle
  have zd := congrArg WGStoreView.dev effect
  change z.dev=some {d with peers:=d.peers.insert pid {p with refcount:=p.refcount+1}} at zd
  have slot := congrFun (congrArg Prod.snd same) pid
  cases ending : mid.dev with
  | none => simp [peerView,ending,zd] at slot
  | some e =>
    cases stored : e.peers[pid]? with
    | none => simp [peerView,ending,zd,stored] at slot
    | some q =>
      have count : q.refcount=p.refcount+1 := by
        simpa [peerView,ending,zd,stored] using congrArg (fun x=>x.map (fun s=>s.2.1)) slot
      exact peerPut_indexCore_held pid mid amid () v b ⟨safe,e,q,ending,stored,by omega⟩ pay

theorem put_key (kid : KeypairId) (pid : PeerId) :
    Hoare (keypairPut (some kid) false) (Held Reached.Core kid pid)
      (fun _=>Credit Reached.Core (some pid)) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  obtain ⟨initial,d,p,k,device,resident,peerCount,key,keyCount⟩ := pre
  have after := (hoare_iff_run_ambient _ _ _).mp (CryptCore.key_release_core (some kid) false)
    w a result v b initial run
  obtain ⟨out,ending,tail,actual,effect⟩ := Config.keypairPut_retained kid d k key keyCount w a device
  rw [run] at actual
  cases actual
  refine ⟨after,?_⟩
  intro selected equal
  cases equal
  exact ⟨Config.withKeypair d kid {k with refcount:=k.refcount-1},p,effect,resident,peerCount⟩

theorem put_peer (peer : Option PeerId) :
    Hoare (peerPut peer) (Credit Reached.Core peer) (fun _=>Reached.Core) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  cases peer with
  | none => cases run; exact pre.1
  | some pid => exact peerPut_indexCore_held pid w a result v b ⟨pre.1,pre.2 pid rfl⟩ run

theorem front (msg : List UInt8) :
    Hoare (do let entry ← indexLookup [.keypair] (u32le msg 4); Affiliation.receiveKeyAcquire entry)
      Reached.Core (DataIngressRules.Acquired Reached.Core (Held Reached.Core) (Credit Reached.Core)) := by
  have lookup : Hoare (indexLookup [.keypair] (u32le msg 4)) Reached.Core
      (fun result w=>Reached.Core w ∧ ∀owner pid,result=some (owner,pid) → ∃kid d p k,
        owner=.keypair kid ∧ w.dev=some d ∧ d.peers[pid]?=some p ∧ 1<p.refcount ∧
        d.keypairs[kid]?=some k ∧ k.peer=some pid ∧ 0<k.refcount) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b pre run
    exact ⟨(indexLookup_indexCore_held [.keypair] (u32le msg 4) w a result v b pre run).1,
      (indexLookup_keypair_held (u32le msg 4) w a result v b (fun d hd=>(pre d hd).2.2.1) run).2⟩

  exact positive_front DeviceIndexCore msg key_acquire_core lookup

theorem core (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    Preserves Reached.Core (consumeData msg src ds) := by
  apply DataIngressRules.preserves Reached.Core (Held Reached.Core) (Credit Reached.Core) msg src ds
    (front msg) (fun _ _ _ h=>h.1) put_key put_peer
  · intro kid pid
    exact held_frame Reached.Core _ (CryptCore.skb _)
      (fun d=>hoare_liftSkb_references_variant _ d) kid pid
  · intro kid pid id
    exact held_frame Reached.Core _ (ConfigurationIndex.frame_core (enqueue_fields id))
      (fun d=>enqueuePerDeviceAndPeerRx_spec_references_variant id d) kid pid
  · intro kid pid id
    exact held_frame Reached.Core _ (publish_core id .dead)
      (fun d=>enqueuePerPeerRx_pure_spec_references_variant id .dead d) kid pid
  · intro id
    exact CryptCore.skb _

theorem ready (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    Preserves TimerCore.Ready (consumeData msg src ds) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (CurrentSlots.consumeData_preserves msg src ds)
    w a result v b pre.1 run,(hoare_iff_run_ambient _ _ _).mp (core msg src ds)
    w a result v b pre.2 run⟩

end Leanux.Proofs.WG.Index.DataIngress
