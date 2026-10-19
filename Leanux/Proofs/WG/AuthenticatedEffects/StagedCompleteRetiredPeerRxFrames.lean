import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerAcquireFrames
import Leanux.Proofs.WG.Queues.HolderPollFrames

/-! Exact RX selection, payment and physical free. Selection keeps its
charge; payment removes that charge; free removes only the paid inventory
cell. Normal source endpoints do not assert a state after a Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open DurableHolders

theorem Upper.key_put (upper : Upper holders carriers loans w) (kid : Option KeypairId) (now : Bool)
    (a b : Ambient) (run : ((keypairPut kid now).run w).run a = .ok (((),v),b)) :
    Upper holders carriers loans v :=
  upper.peer_view (congrArg Prod.fst ((ProjectedAction.iff_run_ambient _ _ _).mp
    (keypairPut_credit_frame kid now) w a () v b run))

theorem Phased.key_put (account : Phased holders carriers loans w) (kid : Option KeypairId) (now : Bool)
    (a b : Ambient) (run : ((keypairPut kid now).run w).run a = .ok (((),v),b)) :
    Phased holders carriers loans v := by
  have frame := (hoare_iff_run_ambient _ _ _).mp (HolderWorkFrames.keypairPut_frame kid now w)
    w a () v b (Frame.refl w) run
  exact ⟨⟨account.funded.aligned.frame frame,keyPut_state kid now account.funded.carriers a b run⟩,
    account.upper.key_put kid now a b run⟩

theorem Phased.receive_payment {c : RxCredits.Carrier}
    (account : Phased holders (c :: carriers) loans w) (selected : c.phase = .selected)
    (a b : Ambient) (run : ((peerPut (some c.owner.slot)).run w).run a = .ok (((),v),b)) :
    Phased holders (paid c :: carriers) loans v := by
  obtain ⟨p,found,_⟩ := selected_credit account.funded.carriers.funded selected
  obtain ⟨d,device,_,stored,_⟩ := resident_fields found
  obtain ⟨funded,rx,_⟩ := selected_payment_normal account.funded.carriers.funded selected a b run
  have keys := (KeyEffects.iff_run_ambient _ _).mp
    (peerPut_keyEffect (allowed := NoPromotion) (some c.owner.slot)) w a () v b run
  have frame := (hoare_iff_run_ambient _ _ _).mp (HolderWorkFrames.peerPut_frame (some c.owner.slot) w)
    w a () v b (Frame.refl w) run
  refine ⟨⟨account.funded.aligned.frame frame,
    inventory_paid (inventory_view account.funded.carriers.inventory rx),
    selected_payment_queues account.funded.carriers.queues selected device stored a b run,
    funded,keys.rxCompatible rx account.funded.carriers.keys.1,
    keys.currentsCompatible account.funded.carriers.keys.2 (fun _ _ h => h.elim)⟩,
    account.upper.receive_payment selected found run⟩

theorem free_rx_peers (id : SkbId) : SameView peerView (freeRxSkb id) := by
  intro initial
  unfold freeRxSkb
  apply hoare_liftSkb
  intro w d store hi device
  simpa only [peerView,device,Option.map_some,Option.bind_some] using hi

theorem free_rx_holders (id : SkbId) (initial : WGWorld) :
    Preserves (Frame initial) (freeRxSkb id) := by
  unfold freeRxSkb
  apply hoare_liftSkb
  intro w d store hi device
  exact hi.trans (by constructor <;> first
    | (simp [passiveView,sendView,device])
    | (intro q xs h; simpa [handoffTxView,device] using h))

theorem Upper.free_rx {c : RxCredits.Carrier}
    (upper : Upper holders (paid c :: carriers) loans w) (a b : Ambient)
    (run : ((freeRxSkb c.packet.slot).run w).run a = .ok (((),v),b)) :
    Upper holders carriers loans v :=
  (upper.peer_view ((ProjectedAction.iff_run_ambient _ _ _).mp
    (free_rx_peers c.packet.slot) w a () v b run)).paid_remove

theorem Phased.free_rx {c : RxCredits.Carrier}
    (account : Phased holders (paid c :: carriers) loans w) (a b : Ambient)
    (run : ((freeRxSkb c.packet.slot).run w).run a = .ok (((),v),b)) :
    Phased holders carriers loans v ∧ packetAt v c.packet = none := by
  obtain ⟨out,actual,inventory,funded,gone⟩ := paid_free a
    account.funded.carriers.inventory account.funded.carriers.funded
  have eq : out = v := by rw [run] at actual; cases actual; rfl
  subst out
  have frame := (hoare_iff_run_ambient _ _ _).mp (free_rx_holders c.packet.slot w)
    w a () v b (Frame.refl w) run
  exact ⟨⟨⟨account.funded.aligned.frame frame,inventory,
    paid_free_queues account.funded.carriers.queues a b run,funded,
    freeRx_keys c.packet.slot account.funded.carriers.keys a b run⟩,
    account.upper.free_rx a b run⟩,gone⟩

/-- Literal key payment, selected peer payment, then physical free restores
the original stable remainder and keeps the same durable holder witness. -/
theorem Phased.cleanup {c : RxCredits.Carrier}
    (account : Phased holders (c :: carriers) loans w) (stable : StableRx carriers w)
    (phase : c.phase = .selected) (owner : pkt.peer = c.owner.slot)
    (a b : Ambient) (run : ((RxCredits.cleanup c.packet.slot pkt flag).run w).run a = .ok (((),v),b)) :
    Account holders carriers loans v ∧ packetAt v c.packet = none := by
  have stableOut := stable_selected_cleanup stable account.funded.carriers phase owner a b run
  unfold RxCredits.cleanup at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨u,keys,ak,keyRun,run⟩ := run
  cases u
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨u,paidWorld,ap,peerRun,run⟩ := run
  cases u
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨ret,checked,ac,branchRun,freeRun⟩ := run
  have keyAccount := account.key_put _ _ a ak keyRun
  have paidAccount := keyAccount.receive_payment phase ak ap (by simpa only [owner] using peerRun)
  have same := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.branch .rxPollFree flag) (fun g => g = paidWorld))
    paidWorld ap ret checked ac rfl branchRun
  subst checked
  obtain ⟨after,gone⟩ := paidAccount.free_rx ac b freeRun
  exact ⟨after.boundary stableOut,gone⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
