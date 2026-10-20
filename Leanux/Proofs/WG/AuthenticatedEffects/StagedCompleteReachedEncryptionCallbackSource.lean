import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedEncryptInteriorInitialized
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerPointLifted

/-! The encryption callback's original head, loop and publication cuts.
The retained return wrapper always uses the callback's original entry world;
the remaining loop keeps its actual ordered unprocessed suffix. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionCallback
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open EncryptionPacket EncryptionInterior EncryptionRun
open HandshakeSecurity.StagedDisposal
set_option maxHeartbeats 600000
variable {packetState : PacketState} {read : RunWitness DataPacket}

theorem tail_source (items : List SkbId) : EncryptionSource.tail ops (some items)=
    (headPrefix items >>= fun (headId,head)=>EncryptionSource.afterHead ops items headId head) := by
  cases selected : items.head? with
  | some first=>exact tail_factor items first selected
  | none=>
    funext w h
    change runPrefix _ w h=runPrefix _ w h
    simp only [headPrefix,Option.isSome_some,selected,bind_assoc,runPrefix_bind,step_eq]
    rfl

theorem head_residual
    (captured : runPrefix (headPrefix items) w h=(.ok ((headId,head),u),middle)) :
    runPrefix (CausalJournal.encrypt (some items)) w h=
      runPrefix (returned w items (loop headId head items .crypted >>= afterLoop items)) u middle := by
  rw [encrypt_run,tail_source,runPrefix_bind,captured]
  dsimp only
  rw [afterHead_factor]
  rfl

theorem loop_residual
    (captured : runPrefix (headPrefix items) w h=(.ok ((headId,head),u),middle))
    (ordered : items=done++rest)
    (walk : Walk headId head done .crypted u middle packetState v last) :
    runPrefix (CausalJournal.encrypt (some items)) w h=
      runPrefix (returned w items (loop headId head rest packetState >>= afterLoop items)) v last := by
  rw [head_residual captured]
  apply returned_congr
  rw [runPrefix_bind,runPrefix_bind,ordered,walk.continuation rest]

theorem read_residual
    (captured : runPrefix (headPrefix items) w h=(.ok ((headId,head),u),middle))
    (ordered : items=done++skb::rest)
    (walk : Walk headId head done .crypted u middle packetState v last)
    (performed : runPrefix (readPrefix skb) v last=(.ok (read,q),events)) :
    runPrefix (CausalJournal.encrypt (some items)) w h=
      runPrefix (packetTail w items headId head rest
        (crypt headId head skb read >>= afterCrypt skb packetState)) q events := by
  rw [loop_residual captured ordered walk]
  apply returned_congr
  simp only [loop_cons,iteration_factor,bind_assoc,runPrefix_bind,performed]
  rfl

theorem write_residual
    (captured : runPrefix (headPrefix items) w h=(.ok ((headId,head),u),middle))
    (ordered : items=done++skb::rest)
    (walk : Walk headId head done .crypted u middle packetState v last)
    (performed : runPrefix (writePrefix headId head skb) v last=(.ok ((read,encrypted),q),events)) :
    runPrefix (CausalJournal.encrypt (some items)) w h=
      runPrefix (packetTail w items headId head rest (writeTail skb packetState encrypted)) q events := by
  rw [loop_residual captured ordered walk]
  apply returned_congr
  simp only [loop_cons,write_factor,bind_assoc,runPrefix_bind,performed]
  rfl

theorem byte_residual
    (captured : runPrefix (headPrefix items) w h=(.ok ((headId,head),u),middle))
    (ordered : items=done++skb::rest)
    (walk : Walk headId head done .crypted u middle packetState v last)
    (prepared : runPrefix (writePrefix headId head skb) v last=(.ok ((read,some bytes),q),events))
    (written : runPrefix (ops.step (liftWG (setTxSkb skb fun p=>{p with bytes}))) q events=(.ok ((),t),after)) :
    runPrefix (CausalJournal.encrypt (some items)) w h=
      runPrefix (returned w items (loop headId head rest packetState >>= afterLoop items)) t after := by
  rw [write_residual captured ordered walk prepared]
  apply returned_congr
  simp only [writeTail,Option.isSome_some,ite_true,Option.getD_some,
    bind_assoc,runPrefix_bind,written]
  rfl

theorem publication_source (items : List SkbId) : EncryptionSource.tail ops (some items)=
    (callbackPublicationPrefix items >>= fun (_,_,packetState)=>publish items packetState) := by
  rw [tail_source]
  simp only [callbackPublicationPrefix,publication_factor,bind_assoc,pure_bind]

theorem publication_residual
    (performed : runPrefix (callbackPublicationPrefix items) w h=(.ok ((headId,head,packetState),u),middle)) :
    runPrefix (CausalJournal.encrypt (some items)) w h=
      runPrefix (returned w items (publish items packetState)) u middle := by
  rw [encrypt_run,publication_source,runPrefix_bind,performed]
  rfl

theorem publication_site_residual
    (entered : runPrefix (callbackPublicationPrefix items) w h=(.ok ((headId,head,packetState),u),middle))
    (performed : runPrefix (publicationPrefixAt site items packetState) u middle=(.ok ((first,pid),v),last)) :
    runPrefix (CausalJournal.encrypt (some items)) w h=
      runPrefix (returned w items (do publicationTailAt site first pid packetState; pure true)) v last := by
  rw [publication_residual entered]
  apply returned_congr
  rw [publish,runPrefix_bind,publication_continuation performed,runPrefix_bind]

theorem release_residual
    (entered : runPrefix (callbackPublicationPrefix items) w h=(.ok ((headId,head,packetState),u),middle))
    (performed : runPrefix (publicationPrefixAt .scheduled items packetState) u middle=(.ok ((first,pid),v),last))
    (point : PeerRetirement.Points.NativePoints (some pid) v last q events) :
    runPrefix (CausalJournal.encrypt (some items)) w h=
      runPrefix (returned w items (do PeerRetirement.Points.continuation point; pure true)) q events := by
  rw [publication_site_residual entered performed]
  apply returned_congr
  change runPrefix (release pid >>= fun _=>pure true) v last=_
  rw [release,runPrefix_bind,runPrefix_bind,PeerRetirement.Points.continuation_run point]

def returnReceipt (item : Option (List SkbId)) (origin : World) (value : Bool) : PrefixM CausalJournal.Event Bool := do
  let current ← liftPrefix get
  emitPrefix (.old (.encryptionReturn item ⟨value,origin,current⟩))
  pure value

theorem pending_return_residual
    (performed : runPrefix (EncryptionSource.tail ops item) w h=(.ok (value,v),last)) :
    runPrefix (CausalJournal.encrypt item) w h=runPrefix (returnReceipt item w value) v last := by
  rw [encrypt_run,performed]
  rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionCallback
