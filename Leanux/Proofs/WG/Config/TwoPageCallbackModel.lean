import Leanux.Proofs.WG.Config.CursorCallbackModel
import Leanux.Proofs.WG.Config.MultiPeerDumpModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config.TwoPage
open Leanux Leanux.WG Noise Lean Std.Do

/-- The peer-map lookup after the first page's actual acquisition. -/
def heldPeers (peers : PeerId → Peer) (cursor id : PeerId) : Peer :=
  if id = cursor then {peers id with refcount := (peers id).refcount+1} else peers id

/-- Exact fitting-prefix composition of the checked greedy peer model. -/
theorem fixedPeersRun_prefix (peers : PeerId → Peer) (front tail : List PeerId)
    (ctx : DumpCtx) (fresh : ctx.nextAllowedip = none) (sequence : ctx.allowedipsSeq = 0)
    (cursor : Option PeerId) (skb : NlSkb) (prior : Array PeerDumpAttrs)
    (fits : multiPeerSpace peers front ≤ skb.room) :
    fixedPeersRun peers (front ++ tail) ctx cursor skb prior =
      fixedPeersRun peers tail ctx ((front.getLast?).or cursor)
        {skb with room := skb.room-multiPeerSpace peers front}
        (prior ++ (multiPeerParts peers front).toArray) := by
  induction front generalizing ctx cursor skb prior with
  | nil => simp [multiPeerSpace,multiPeerParts]
  | cons pid front ih =>
    have one : peerFixedSpace (peers pid) ≤ skb.room := by
      simp only [multiPeerSpace,List.map_cons,List.sum_cons] at fits
      omega
    have rest : multiPeerSpace peers front ≤ skb.room-peerFixedSpace (peers pid) := by
      simp only [multiPeerSpace,List.map_cons,List.sum_cons] at fits ⊢
      omega
    have reset : {ctx with nextAllowedip := none,allowedipsSeq := 0} = ctx := by
      cases ctx; simp_all
    simp only [List.cons_append,fixedPeersRun,ite_eq_left one,reset]
    rw [ih ctx fresh sequence (some pid) _ _ rest]
    have parts : prior.push {publicKey := hexKey (peers pid).remoteStatic,attrs := peerFixedAttrs (peers pid)} ++
        (multiPeerParts peers front).toArray = prior ++ (multiPeerParts peers (pid::front)).toArray := by
      change prior.push _ ++ (front.map _).toArray = prior ++ ((_ :: front.map _).toArray)
      rw [List.toArray_cons,Array.push_eq_append,Array.append_assoc]
    rw [parts]
    cases front <;> simp only [multiPeerSpace,List.map_cons,List.sum_cons,List.getLast?,Nat.sub_sub]
    all_goals rfl

/-- A maximal fitting nonempty prefix is emitted, and the next peer is cancelled. -/
theorem fixedPeersRun_firstSplit (peers : PeerId → Peer) (before : List PeerId)
    (cursor next : PeerId) (tail : List PeerId) (skb : NlSkb)
    (fits : multiPeerSpace peers (before ++ [cursor]) ≤ skb.room)
    (short : skb.room-multiPeerSpace peers (before ++ [cursor]) < peerFixedSpace (peers next)) :
    fixedPeersRun peers ((before ++ [cursor]) ++ next :: tail)
      {hasWg := true} none skb #[] =
      ({hasWg := true},some cursor,
       {skb with room := skb.room-multiPeerSpace peers (before ++ [cursor])},false,
       (multiPeerParts peers (before ++ [cursor])).toArray) := by
  rw [fixedPeersRun_prefix peers (before ++ [cursor]) (next::tail) _ rfl rfl none skb #[] fits]
  have notFit : ¬peerFixedSpace (peers next) ≤ skb.room-multiPeerSpace peers (before ++ [cursor]) := by omega
  simp [fixedPeersRun,notFit]

/-- Every fitting remaining peer completes; references are handled by the actual finalizer. -/
theorem fixedPeersRun_complete (peers : PeerId → Peer) (ids : List PeerId)
    (ctx : DumpCtx) (fresh : ctx.nextAllowedip = none) (sequence : ctx.allowedipsSeq = 0)
    (cursor : Option PeerId) (skb : NlSkb) (prior : Array PeerDumpAttrs)
    (fits : multiPeerSpace peers ids ≤ skb.room) :
    fixedPeersRun peers ids ctx cursor skb prior =
      (ctx,(ids.getLast?).or cursor,{skb with room := skb.room-multiPeerSpace peers ids},true,
        prior ++ (multiPeerParts peers ids).toArray) := by
  simpa [fixedPeersRun] using fixedPeersRun_prefix peers ids [] ctx fresh sequence cursor skb prior fits

/-- The resumed cursor uses its first occurrence; freshness is only required
before that boundary, not throughout the peer list. -/
theorem cursorSelected_boundary (d : Device) (before tail : List PeerId) (cursor : PeerId)
    (members : d.peerList = before ++ cursor :: tail) (fresh : cursor ∉ before) :
    cursorSelected d {hasWg := true,nextPeer := some cursor} = tail := by
  simp only [cursorSelected,members]
  have drop : (before ++ cursor :: tail).dropWhile (· != cursor) = cursor :: tail := by
    clear members
    induction before with
    | nil => simp
    | cons id before ih =>
      have ne : id ≠ cursor := by intro eq; subst id; simp at fresh
      have rest : cursor ∉ before := by simp_all
      simp [ne,ih rest]
  rw [drop]
  rfl

end Leanux.Proofs.WG.Config.TwoPage
