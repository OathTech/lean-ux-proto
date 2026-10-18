import Leanux.Proofs.WG.Index.PollCoreEffects

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.PollCore
open Leanux Leanux.WG Noise Queues Queues.RxCredits
open Queues.RxCredits.DurableHolders Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

theorem store_ready {α : Type} {action : WG.M α} (same : SameWGStore action) :
    Preserves TimerCore.Ready action :=
  ReceiveCompletion.ready_join _ (CurrentSlots.store_preserves same)
    (ConfigurationIndex.frame_core (ReceiveCompletion.store_fields same))

theorem packet_ready {α : Type} (action : SkbM α) :
    Preserves TimerCore.Ready (liftSkb action) :=
  ReceiveCompletion.ready_join _ (by
    apply hoare_liftSkb
    intro w d store pre device
    apply CurrentSlots.fields_transport pre
    unfold CurrentSlots.fields RxCredits.keyWords
    simp only [device,Option.map_some,Option.bind_some])
    (CryptCore.skb action)

theorem peer_update_ready (pid : PeerId) (f : Peer→Peer)
    (cell : ∀p,senderPeerCell (f p)=senderPeerCell p)
    (slots : ∀p,Affiliation.peerCell (f p)=Affiliation.peerCell p) :
    Preserves TimerCore.Ready (modifyPeer pid f) :=
  ReceiveCompletion.ready_join _
    ((pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotTraffic.«0».Leanux.Proofs.WG.CurrentSlots.update_peer) pid f slots)
    (ConfigurationIndex.frame_core (ConfigurationIndex.modifyPeer_fields pid f cell))

end Leanux.Proofs.WG.Index.PollCore
