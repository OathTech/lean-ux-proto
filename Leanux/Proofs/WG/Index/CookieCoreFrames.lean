import Leanux.Proofs.WG.Index.CookieCoreModel
import Leanux.Proofs.WG.Index.ConfigurationIndexFrames
import Leanux.Proofs.WG.Index.OwnerCoherenceHeldFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits Queues.RxCredits.DurableHolders

theorem modifyPeer_indexCoreHeld (pid : PeerId) (f : Peer → Peer)
    (same : ∀ p,senderPeerCell (f p)=senderPeerCell p)
    (word : ∀ p,(f p).handshakeEntryPeer=p.handshakeEntryPeer)
    (count : ∀ p,(f p).refcount=p.refcount) :
    Ensures (modifyPeer pid f) (IncomingCoreHeld pid) (fun _ => IncomingCoreHeld pid) := by
  intro g a result out b pre run
  have core := (hoare_iff_run_ambient _ _ _).mp
    (ConfigurationIndex.frame_core (ConfigurationIndex.modifyPeer_fields pid f same))
    g a result out b pre.1 run
  have held := modifyPeer_ownerHeld pid pid f word count g a result out b
    ⟨fun d device => (pre.1 d device).2.2.1,pre.2⟩ run
  exact ⟨core,held.2⟩


end Leanux.Proofs.WG.Index
