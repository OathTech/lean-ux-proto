import Leanux.Proofs.WG.RetirementSecurity.ReadySocketHead

/-! The actual worker tests its selected head before entering completion.
The checked branch result, rather than an assumed ready flag, authorizes the
complete-byte batch passed to the socket observer. -/
namespace Leanux.Proofs.WG.RetirementSecurity.ReadySocket
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity Completion ReadyCiphertext
set_option maxHeartbeats 600000

theorem stop (s : String) : PrefixPreserves (Inv P) Good
    (liftPrefix (liftWG (invariant s : WG.M α))) := by
  apply lift_safe
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  cases run

def check (first : Option (List SkbId)) : PrefixM Completion.Event Bool :=
  TxDisposition.andObs (liftPrefix (liftWG (Leanux.branch .txPacket first.isSome))) do
    let some f:=first | liftPrefix (liftWG (invariant "unreachable"))
    let some h:=f.head? | liftPrefix (liftWG (invariant "an empty ring item"))
    liftPrefix (liftWG (Leanux.branch .txNotUncrypted ((←Completion.access (getTxSkbPrefix h)).state != .uncrypted)))

theorem check_safe (first : Option (List SkbId)) : PrefixPreserves (Inv (ReadyHead items)) Good (check first) := by
  unfold check TxDisposition.andObs
  apply PrefixPreserves.bind (ReadySocket.branch .txPacket first.isSome)
  intro bit
  cases bit with
  | false=>exact PrefixPreserves.pure (fun _ _ before=>before.2) false
  | true=>
    simp only [ite_true]
    cases first with
    | none=>exact stop "unreachable"
    | some xs=>
      simp only
      cases head:xs.head? with
      | none=>exact stop "an empty ring item"
      | some id=>
        apply PrefixPreserves.bind (access (getTxSkbPrefix_erases id) (head_frame (packets_read id)))
        intro packet
        exact ReadySocket.branch .txNotUncrypted (packet.state != .uncrypted)

theorem drop_guarded (peer : PeerId) (ids : List SkbId) :
    PrefixPreserves (Inv (Guarded items state)) Good
      (focusPrefix Completion.Event.disposition Completion.disposition? (TxDisposition.drop peer ids)) :=
  quiet (Appends.focus _ _ _) (focusPrefix_other _ _ _ (fun _=>rfl) _)
    (focusPrefix_erases _ _ (TxDisposition.drop_erases peer ids))
    (PublicationPoll.native_product _ _ (guarded_frame (complete_frame (drop_packets peer))))

theorem dispose (peer : PeerId) (ids : List SkbId) (key : KeypairId) :
    PrefixPreserves (Inv (Guarded items state)) Good
      (focusPrefix Completion.Event.disposition Completion.disposition? (TxDisposition.dispose peer ids key)) :=
  quiet (Appends.focus _ _ _) (focusPrefix_other _ _ _ (fun _=>rfl) _)
    (focusPrefix_erases _ _ (TxDisposition.dispose_erases peer ids key))
    (PublicationPoll.native_product _ _ (dispose_guarded peer ids key))

theorem finish (pid : PeerId) (items : List SkbId) (packet : DataPacket) :
    PrefixPreserves (Inv (Guarded items packet.state)) Good (do
      focusPrefix Completion.Event.disposition Completion.disposition? (TxDisposition.drop pid items)
      if ←liftPrefix (liftWG (Leanux.branch .txCrypted (packet.state==.crypted))) then Completion.complete pid items
      focusPrefix Completion.Event.disposition Completion.disposition? (TxDisposition.dispose pid items packet.keypair)) := by
  apply PrefixPreserves.bind (drop_guarded pid items)
  intro _
  apply PrefixEnsures.preserves
  apply PrefixEnsures.bind (branch_checked .txCrypted (packet.state==.crypted))
  intro bit w h before
  have tail : PrefixPreserves (Inv (Guarded items packet.state)) Good (do
      if bit then Completion.complete pid items
      focusPrefix Completion.Event.disposition Completion.disposition? (TxDisposition.dispose pid items packet.keypair)) := by
    cases bit with
    | false=>exact dispose pid items packet.keypair
    | true=>
      have yes:packet.state=.crypted:=by
        cases mark:packet.state with
        | crypted=>rfl
        | uncrypted=>
          have h:(PacketState.uncrypted==PacketState.crypted)=true:=by simpa only [mark] using before.1.symm
          have no:(PacketState.uncrypted==PacketState.crypted)=false:=by decide
          rw [no] at h
          cases h
        | dead=>
          have h:(PacketState.dead==PacketState.crypted)=true:=by simpa only [mark] using before.1.symm
          have no:(PacketState.dead==PacketState.crypted)=false:=by decide
          rw [no] at h
          cases h
      apply PrefixPreserves.bind
      · apply (show PrefixEnsures (Inv (Complete items)) Good (Completion.complete pid items)
          (fun _=>Inv (Complete items)) from complete pid items).consequence
        · intro h w initial
          exact ⟨initial.1 yes,initial.2⟩
        · intro result h w final
          exact ⟨fun _=>final.1,final.2⟩
      · intro _
        exact dispose pid items packet.keypair
  exact tail w h before.2

theorem body_some (pid : PeerId) (items : List SkbId) :
    PrefixEnsures (Inv (ReadyHead items)) Good (Completion.body pid (some items)) (fun _ h _=>Good h) := by
  unfold Completion.body
  apply PrefixEnsures.bind (check_safe (some items))
  intro go
  cases go with
  | false=>exact PrefixEnsures.pure (fun _ _ before=>before.2) (fun _ _ before=>before.2)
  | true=>
    simp only [Bool.not_true,Bool.false_eq_true,ite_false]
    cases head:items.head? with
    | none=>
      apply (show PrefixEnsures (Inv (ReadyHead items)) Good
        (liftPrefix (liftWG (invariant "an empty ring item" : WG.M Bool)))
        (fun _=>Inv (ReadyHead items)) from stop "an empty ring item").consequence
      · intro _ _ before; exact before
      · intro _ _ _ after; exact after.2
    | some id=>
      apply PrefixEnsures.bind (head_read items id head)
      intro packet
      apply (show PrefixEnsures (Inv (Guarded items packet.state)) Good _
        (fun _=>Inv (Guarded items packet.state)) from finish pid items packet).consequence
      · intro _ _ before; exact before
      · intro _ _ _ after; exact after.2

end Leanux.Proofs.WG.RetirementSecurity.ReadySocket
