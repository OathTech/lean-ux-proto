import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedWorkerHooks
import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedCompletion

/-! The actual encryption continuation changes packet bytes and TX scheduling,
while preserving live handshake-work and timer occurrences. Native checksum
and padding callbacks retain their existing product-world frames. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do
open TransmitSecurity TimerSlots Queues
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem product_native (action : Leanux.M α)
    (safe : ∀ h, Preserves (fun w : World => Inv h w.wg) action) : ProductSafe (liftPrefix action) :=
  PrefixEnsures.lift _ (fun _ _ _ => True.intro)
    (fun h w value v hi run => (hoare_iff_run _ _ _).mp (safe h) w value v hi run)

theorem observed_product (body : PrefixM Event α) (native : Leanux.M α)
    (erases : ErasesPrefix body native) (appends : Appends body)
    (safe : ∀ h, Preserves (fun w : World => Inv h w.wg) native) : ProductSafe body := by
  intro w h hi
  obtain ⟨suffix,grown⟩ := appends w h
  refine ⟨suffix,grown,True.intro,?_⟩
  cases run : (runPrefix body w h).1 with
  | error _ => trivial
  | ok value =>
    have original := (erases w h).symm.trans run
    have output := (hoare_iff_run _ _ _).mp (safe h) w value.1 value.2 hi original
    rw [grown]
    exact output.append suffix

theorem native_product_contract (action : WG.M α) (safe : StateSafe (liftWGPrefix action)) (h : List Event) :
    Preserves (fun w : World => Inv h w.wg) (liftWG action) :=
  PublicationPoll.native_product (Inv h) _ (native_contract action safe h)

private theorem enqueue_tx (items : List SkbId) (state : PacketState) :
    StateSafe (liftWGPrefix (enqueuePerPeerTx items state)) :=
  state_framed _
    ((pinned_const _private.Leanux.Proofs.WG.AuthenticatedEffects.TimerSendFrames.«0».Leanux.Proofs.WG.AuthenticatedEffects.TimerSlots.enqueue_peer_retained) items state)
    (SendWorkCauses.of_workQueueFrame
      ((pinned_const _private.Leanux.Proofs.WG.AuthenticatedEffects.SendQueueDataFrames.«0».Leanux.Proofs.WG.AuthenticatedEffects.SendWorkCauses.enqueue_peer_frame) items state))

private theorem packet (kid : KeypairId) (pkt : DataPacket) (h : List Event) :
    Preserves (fun w : World => Inv h w.wg) (encryptPacket Env.checksumHelp kid pkt) := by
  let P := fun w : World => Inv h w.wg
  change Preserves P _
  have clock {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have padding : Preserves P (monadLift (calculateSkbPadding pkt.plaintext.bytes.length pkt.plaintext.mtu) : Leanux.M Nat) :=
    native_product_contract _ (state_framed _
      (fun initial => (calculateSkbPadding_sameWGWorld _ _).wp (Retained initial))
      ((calculateSkbPadding_sameWGWorld _ _).factor QueuedOccurrences.queue)) h
  have checksum (p : Packet) : Preserves P (Env.checksumHelp p) := (checksumHelp_sameWorld p).wp P
  have key : Preserves P (monadLift (getKeypair kid) : Leanux.M Keypair) :=
    native_product_contract (getKeypair kid : WG.M Keypair) (by causal_delayed_native) h
  routing_tx_source [encryptPacket] using [clock,padding,checksum,key]

theorem encrypt_native (item : Option (List SkbId)) (h : List Event) :
    Preserves (fun w : World => Inv h w.wg) (RxWorkers.encryptStepTailSource item) := by
  let P := fun w : World => Inv h w.wg
  change Preserves P _
  have clock {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have read (id : SkbId) : Preserves P (monadLift (getTxSkb id) : Leanux.M DataPacket) :=
    native_product_contract _ (by unfold getTxSkb; exact skb _) h
  have write (id : SkbId) (f : DataPacket → DataPacket) : Preserves P (monadLift (setTxSkb id f) : Leanux.M Unit) :=
    native_product_contract _ (by unfold setTxSkb; exact skb _) h
  have publish (items : List SkbId) (state : PacketState) : Preserves P (monadLift (enqueuePerPeerTx items state) : Leanux.M Unit) :=
    native_product_contract _ (enqueue_tx items state) h
  have crypt (kid : KeypairId) (pkt : DataPacket) : Preserves P (encryptPacket Env.checksumHelp kid pkt) := packet kid pkt h
  routing_tx_source [RxWorkers.encryptStepTailSource] using [read,write,publish,crypt,clock]

theorem encrypt (item : Option (List SkbId)) : ProductSafe (hooks.encrypt item) := by
  apply observed_product _ (RxWorkers.encryptStepTailSource item)
  · apply CallbackFrames.product_erases old? (CausalJournal.encrypt_projects item)
    intro w h
    have projected := congrArg Prod.fst (Journal.encrypt_projects item w h)
    have maps : (fun x : Bool × World => (id x.1,x.2)) = id := by funext ⟨value,v⟩; rfl
    rw [maps,Except.map_id] at projected
    exact projected.symm
  · exact (CallbackQuiet.encrypt (fun _ : Event => (none : Option Empty))
      (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) item).1
  · exact encrypt_native item

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
