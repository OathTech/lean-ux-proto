import Leanux.Proofs.WG.Config.PeerMixedGetterFrames
import Leanux.Proofs.WG.Config.PeerKeyGetterFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- Actual source/cache resets disappear only from the getter's explicit data
view; every absent entry and the ordered selected scalar writes are retained. -/
theorem multiMixedEffect_getter_view (d current : Device) (mark : Nat) (pid : PeerId)
    (p : Peer) (psk : Key) (interval : Nat)
    (effect : MultiMixedEffect d mark pid psk interval current)
    (resident : d.peers[pid]? = some p) :
    ∀ q : PeerId, (current.peers[q]?).map keyGetterPeerView =
      ((scalarRequestDevice {d with fwmark := mark} pid p psk interval).peers[q]?).map keyGetterPeerView := by
  intro q
  cases original : d.peers[q]? with
  | none =>
    have different : q ≠ pid := by intro eq; subst q; rw [resident] at original; cases original
    obtain ⟨cleared,selected,_,clears,selectedResident,rfl⟩ := effect
    have absent : cleared.peers[q]? = none := by
      by_cases member : q ∈ d.peerList
      · have h := clears q
        simp only [member,ite_true] at h
        obtain ⟨old,reset,before,_⟩ := h
        rw [original] at before
        cases before
      · have h := clears q
        simpa only [member,ite_false,original] using h
    simp [scalarDevice,scalarRequestDevice,withPeer,Std.TreeMap.getElem?_insert,Ne.symm different,absent,original]
  | some old =>
    obtain ⟨next,found,ips,key,attrs⟩ := multiMixedEffect_peer d current mark pid q psk interval old effect original
    obtain ⟨next',found',refs,dead,cost⟩ := multiMixedEffect_cursor_fields d current mark pid q psk interval old effect original
    have eq : next' = next := Option.some.inj (found'.symm.trans found)
    subst next'
    rw [found]
    by_cases same : q = pid
    · subst q
      have oldEq : old = p := Option.some.inj (original.symm.trans resident)
      subst old
      simp only [ite_true] at attrs
      have cost' : peerFixedSpace next = peerFixedSpace {p with presharedKey := psk,persistentKeepaliveInterval := interval} := cost
      simp [scalarRequestDevice,scalarDevice,withPeer,keyGetterPeerView,key,attrs,cost',ips,refs,dead]
    · simp only [same,ite_false] at attrs
      simp [scalarRequestDevice,scalarDevice,withPeer,Std.TreeMap.getElem?_insert,Ne.symm same,original,
        keyGetterPeerView,key,attrs,cost,ips,refs,dead]


end Leanux.Proofs.WG.Config
