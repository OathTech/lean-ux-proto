import Leanux.Proofs.WG.RetirementSecurity.TransmitEntryOccurrences
import Leanux.Proofs.WG.RetirementSecurity.RxCompletionHolders
import Leanux.Proofs.WG.RetirementSecurity.RxCompletionOccurrences
import Leanux.Proofs.WG.TransmitSecurity.DriverStagingProjection
import Leanux.Proofs.WG.TransmitSecurity.DriverSpecialization

/-! Ownership contracts for the shared campaign driver. Its checked exact
projection to the nonce specialization recovers each original native run.
These are source-cut endpoint contracts; they do not infer internal event
chronology from erasure or claim initialized whole-driver ownership closure. -/
namespace Leanux.Proofs.WG.RetirementSecurity.DriverOwnership
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity
variable {E : Type} {ρ : E → Option Nonce.Allocation} {hooks : Driver.Hooks E}

def Boundary (temporary : Credits.Ledger) (locals : List TxLocalBatch)
    (active : List (List SkbId)) (w : WGWorld) : Prop :=
  HolderAccount temporary w ∧ TxInventory locals w ∧ TxCryptInventory active w

theorem initial (net bare : Bool) : Boundary [] [] [] (Runner.initialWG net bare) :=
  ⟨initial_holder_account net bare,initial_tx_inventory net bare,initial_tx_crypt_inventory net bare⟩

theorem state_native {E F α : Type} {ρ : E → Option F} {observer : WGPrefix E α}
    {reference : WGPrefix F α} {native : WG.M α} {result : α}
    (projects : StateProjectsPrefix ρ id observer reference)
    (erases : ErasesStatePrefix reference native) (w v : WGWorld) (a b : Ambient) (h : List E)
    (run : (runWGPrefix observer w a h).1 = .ok ((result,v),b)) :
    ((native.run w).run a) = .ok ((result,v),b) := by
  have projected := congrArg Prod.fst (projects w a h)
  change (runWGPrefix reference w a (h.filterMap ρ)).1 =
    ((runWGPrefix observer w a h).1.map (fun ((x,u),c) => ((id x,u),c))) at projected
  rw [run] at projected
  have erased := erases w a (h.filterMap ρ)
  exact erased.symm.trans projected

theorem product_native {E F α : Type} {ρ : E → Option F} {observer : PrefixM E α}
    {reference : PrefixM F α} {native : Leanux.M α} {result : α}
    (projects : ProjectsPrefix ρ id observer reference)
    (erases : ErasesPrefix reference native) (w v : World) (h : List E)
    (run : (runPrefix observer w h).1 = .ok (result,v)) :
    native.run w = .ok (result,v) := by
  have projected := congrArg Prod.fst (projects w h)
  rw [run] at projected
  have erased := erases w (h.filterMap ρ)
  exact erased.symm.trans projected

theorem staging (projects : Driver.HooksProjects ρ hooks Driver.nonceHooks)
    (before : Boundary temporary locals active w) (bounded : Packets.Inv w)
    (compatible : RxCredits.CurrentCompatible pid w) (a b : Ambient) (h : List E)
    (run : (runWGPrefix (Driver.stagingObserved hooks pid) w a h).1 = .ok (((),v),b)) :
    Boundary temporary locals active v := by
  have projected := Driver.staging_projects projects pid
  rw [Driver.nonce_staging_specialization] at projected
  have native := state_native projected (Nonce.stagingObserved_erases pid) w v a b h run
  have physical := CryptStaging.staged ⟨⟨bounded,before.2.1⟩,before.2.2⟩ pid a b native
  exact ⟨before.1.staged bounded compatible a b native,physical⟩

theorem poll (projects : Driver.HooksProjects ρ hooks Driver.nonceHooks)
    (crypt : TxCryptInventory active w.wg) (h : List E)
    (run : (runPrefix hooks.poll w h).1 = .ok (item,v)) :
    TxCryptInventory (item.toList ++ active) v.wg := by
  have native := product_native projects.poll (erasesPrefix_lift (liftWG TxRing.pollSource)) w v h run
  change ((TxRing.pollSource.run w.wg).run w.ambient).map
    (fun ((out,g),a) => (out,{w with wg := g,ambient := a})) = .ok (item,v) at native
  cases performed : ((TxRing.pollSource.run w.wg).run w.ambient) with
  | error stop => simp [performed,Except.map] at native
  | ok output =>
    obtain ⟨⟨out,g⟩,a⟩ := output
    simp only [performed,Except.map,Except.ok.injEq,Prod.mk.injEq] at native
    obtain ⟨rfl,rfl⟩ := native
    exact crypt.poll w.ambient a performed

theorem encryption (projects : Driver.HooksProjects ρ hooks Driver.nonceHooks)
    (before : Boundary temporary locals (items :: active) w.wg) (h : List E)
    (run : (runPrefix (hooks.encrypt (some items)) w h).1 = .ok (result,v)) :
    Boundary temporary locals active v.wg := by
  have native := product_native (projects.encrypt (some items))
    (erasesPrefix_lift (RxWorkers.encryptStepTailSource (some items))) w v h run
  have accounts := (hoare_iff_run _ _ _).mp (encrypt_tail_accounts (some items))
    w result v ⟨before.1,before.2.1⟩ native
  exact ⟨accounts.1,accounts.2,before.2.2.complete native⟩

theorem transmit (projects : Driver.HooksProjects ρ hooks Driver.nonceHooks)
    (before : Boundary temporary locals active w.wg) (funded : PeerReleaseFunded pid w.wg)
    (h : List E) (run : (runPrefix (hooks.transmit pid) w h).1 = .ok (result,v)) :
    Boundary temporary locals active v.wg := by
  have native := product_native (projects.transmit pid) (erasesPrefix_lift (liftWG (txStep pid))) w v h run
  change (((txStep pid).run w.wg).run w.ambient).map
    (fun ((out,g),a) => (out,{w with wg := g,ambient := a})) = .ok (result,v) at native
  cases performed : (((txStep pid).run w.wg).run w.ambient) with
  | error stop => simp [performed,Except.map] at native
  | ok output =>
    obtain ⟨⟨out,g⟩,a⟩ := output
    simp only [performed,Except.map,Except.ok.injEq,Prod.mk.injEq] at native
    obtain ⟨rfl,rfl⟩ := native
    exact ⟨before.1.tx_step (before.2.1.separated pid) funded w.ambient a performed,
      before.2.1.step pid w.ambient a performed,before.2.2.step before.2.1 pid w.ambient a performed⟩

theorem confirmation (projects : Driver.HooksProjects ρ hooks Driver.nonceHooks)
    (account : HolderAccount temporary w) (a b : Ambient) (h : List E)
    (run : (runWGPrefix (hooks.confirmation pid kid) w a h).1 = .ok ((result,v),b)) :
    HolderAccount temporary v :=
  account.confirm pid kid a b
    (state_native (projects.confirmation pid kid) (erasesStatePrefix_lift _) w v a b h run)

theorem session (projects : Driver.HooksProjects ρ hooks Driver.nonceHooks)
    (account : HolderAccount temporary w) (allocation : AllocationInv history w)
    (a b : Ambient) (h : List E)
    (run : (runWGPrefix (hooks.session pid) w a h).1 = .ok ((result,v),b)) :
    HolderAccount temporary v :=
  account.session allocation pid a b
    (state_native (projects.session pid) (erasesStatePrefix_lift _) w v a b h run)

theorem receive_completion (projects : Driver.HooksProjects ρ hooks Driver.nonceHooks)
    (account : HolderAccount temporary w) (bounded : Packets.Inv w)
    (compatible : RxCredits.KeyCompatible pid pkt.keypair w) (ep : Endpoint)
    (a b : Ambient) (h : List E)
    (run : (runWGPrefix (Driver.consumeObserved hooks pid pkt ep) w a h).1 = .ok ((result,v),b)) :
    HolderAccount temporary v := by
  have projected := Driver.consume_projects projects pid pkt ep
  rw [Driver.nonce_consumeObserved_eq] at projected
  exact account.receive_done bounded compatible ep a b
    (state_native projected (Nonce.consumeObserved_erases pid pkt ep) w v a b h run)

theorem receive_joint (projects : Driver.HooksProjects ρ hooks Driver.nonceHooks)
    (before : Boundary temporary locals active w) (bounded : Packets.Inv w)
    (compatible : RxCredits.KeyCompatible pid pkt.keypair w) (ep : Endpoint)
    (a b : Ambient) (h : List E)
    (run : (runWGPrefix (Driver.consumeObserved hooks pid pkt ep) w a h).1 = .ok ((result,v),b)) :
    Boundary temporary locals active v := by
  have projected := Driver.consume_projects projects pid pkt ep
  rw [Driver.nonce_consumeObserved_eq] at projected
  have native := state_native projected (Nonce.consumeObserved_erases pid pkt ep) w v a b h run
  exact ⟨before.1.receive_done bounded compatible ep a b native,
    receive_done_occurrences before.2 bounded pid pkt ep a b native⟩

theorem transmit_entry (projects : Driver.HooksProjects ρ hooks Driver.nonceHooks)
    (before : Boundary temporary locals active w) (bounded : Packets.Inv w)
    (compatible : RxCredits.CurrentsCompatible w)
    (family addr : Nat) (packets : List Packet) (mtu : Nat) (a b : Ambient) (h : List E)
    (run : (runWGPrefix (Driver.transmitObserved hooks family addr packets mtu) w a h).1 =
      .ok ((result,v),b)) : Boundary temporary locals active v := by
  have projected := Driver.transmit_projects projects family addr packets mtu
  rw [Driver.nonce_transmitObserved_eq] at projected
  have native := state_native projected (Nonce.transmitObserved_erases family addr packets mtu)
    w v a b h run
  exact ⟨before.1.transmit bounded compatible family addr packets mtu a b native,
    TransmitOccurrences.transmit ⟨bounded,before.2⟩ family addr packets mtu a b native⟩

end Leanux.Proofs.WG.RetirementSecurity.DriverOwnership
