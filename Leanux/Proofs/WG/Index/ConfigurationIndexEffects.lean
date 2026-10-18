import Leanux.Proofs.WG.Index.ConfigurationIndexModel
import Leanux.Proofs.WG.Index.SenderIndexEffects

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ConfigurationIndex
open Leanux Leanux.WG Noise Queues Queues.RxCredits
open Queues.RxCredits.DurableHolders Leanux.Proofs.Framing Lifetimes Std.Do
open Leanux.Proofs.WG.Configuration

theorem deviceFields_core (d e : Device) (same : deviceFields e=deviceFields d)
    (pre : DeviceIndexCore d) : DeviceIndexCore e := by
  have cursor : e.nextKeypairId=d.nextKeypairId := congrArg Prod.fst same
  have cell : senderDeviceCell e=senderDeviceCell d := congrArg Prod.snd same
  have table : e.indexTable=d.indexTable := congrArg Prod.fst cell
  have transported := senderDeviceCell_transports d e [] 0 cell
  refine ⟨?_,transported.1 pre.2.1,senderDeviceCell_coherent d e cell pre.2.2.1,
    transported.2.1 pre.2.2.2⟩
  exact ⟨table ▸ pre.1.1,table ▸ pre.1.2.1,
    fun entry member kid owner => cursor ▸ pre.1.2.2 entry (table ▸ member) kid owner⟩

theorem fields_core (w v : WGWorld) (same : fields v=fields w)
    (pre : Reached.Core w) : Reached.Core v := by
  intro e current
  have observed : w.dev.map deviceFields=some (deviceFields e) := by
    change fields w = some (deviceFields e)
    rw [←same]; simp [fields,current]
  obtain ⟨d,found,cell⟩ := Option.map_eq_some_iff.mp observed
  exact deviceFields_core d e cell.symm (pre d found)

theorem deviceFields_peerWrite (d : Device) (pid : PeerId) (p q : Peer)
    (resident : d.peers[pid]?=some p) (same : senderPeerCell q=senderPeerCell p) :
    deviceFields {d with peers:=d.peers.insert pid q}=deviceFields d :=
  Prod.ext rfl (senderFields_peerWrite d pid p q resident same)

end Leanux.Proofs.WG.Index.ConfigurationIndex
