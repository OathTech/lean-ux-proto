import Leanux.Proofs.WG.Index.CallbackRulesSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do

namespace CallbackRules
theorem tableContracts (pid : PeerId) : Contracts pid TablesSafeWG TablesSafeWG :=
  ⟨(ensures_iff _ _ _).mpr (modifyPeer_tables pid _),
   (ensures_iff _ _ _).mpr (modifyPeer_tables pid _),
   (ensures_iff _ _ _).mpr (clearPeerEndpointSrc_tables pid),
   (ensures_iff _ _ _).mpr (purgeStagedPackets_tables pid),
   (ensures_iff _ _ _).mpr (delTimer_tables pid .sendKeepalive),
   fun site timer delay => (ensures_iff _ _ _).mpr (modPeerTimer_tables site pid timer delay),
   fun retry => (ensures_iff _ _ _).mpr (sendQueuedHandshakeInitiation_tables pid retry),
   sendKeepalive_tables pid,
   (ensures_iff _ _ _).mpr (peerGet_tables pid),
   (ensures_iff _ _ _).mpr (peerPut_tables (some pid)),
   (ensures_iff _ _ _).mpr (modifyClearWorkQueue_tables (fun queue => queue++[pid]))⟩
end CallbackRules

theorem expiredRetransmitHandshake_tables (pid : PeerId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ expiredRetransmitHandshake pid
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ :=
  (ensures_iff _ _ _).mp (CallbackRules.retransmit (CallbackRules.tableContracts pid))

theorem expiredSendKeepalive_tables (pid : PeerId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ expiredSendKeepalive pid
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ :=
  (ensures_iff _ _ _).mp (CallbackRules.keepalive (CallbackRules.tableContracts pid))

theorem expiredNewHandshake_tables (pid : PeerId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ expiredNewHandshake pid
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ :=
  (ensures_iff _ _ _).mp (CallbackRules.newHandshake (CallbackRules.tableContracts pid))

theorem expiredZeroKeyMaterial_tables (pid : PeerId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ expiredZeroKeyMaterial pid
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ :=
  (ensures_iff _ _ _).mp (CallbackRules.zero (CallbackRules.tableContracts pid))

theorem expiredSendPersistentKeepalive_tables (pid : PeerId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ expiredSendPersistentKeepalive pid
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ :=
  (ensures_iff _ _ _).mp (CallbackRules.persistent (CallbackRules.tableContracts pid))

theorem timerCallback_tables (pid : PeerId) (timer : PeerTimer) :
    Ensures (timerCallback pid timer) TablesSafeWG (fun _ => TablesSafeWG) :=
  CallbackRules.callback (CallbackRules.tableContracts pid) timer

end Leanux.Proofs.WG.Index
