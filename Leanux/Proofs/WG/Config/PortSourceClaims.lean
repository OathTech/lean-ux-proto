import Leanux.Proofs.WG.Config.ZeroPort
import Leanux.Proofs.WG.Config.RecordedPort
import Leanux.Proofs.WG.Config.FwmarkEffects
import Leanux.Proofs.WG.Config.ClearedSources
import Leanux.Proofs.WG.Config.ClaimView
import Leanux.Proofs.WG.Campaign2.Bridge

/-! Existing socket, port and source-clearing claims over the campaign projection. -/
namespace Leanux.Proofs.WG.Config.SourceClaims
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

theorem original_endpoint_source_clear (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Campaign2.Ensures (clearPeerEndpointSrc pid) (fun w => w.wg.device = some d)
      (fun _ w => ∃ d' reset, w.wg.device = some d' ∧
        d' = { d with peers := d'.peers } ∧
        d'.peers[pid]? = some (clearedSource p reset) ∧
        ∀ q, q ≠ pid → d'.peers[q]? = d.peers[q]?) :=
  clearEndpointSource_exact pid d p resident

theorem original_fwmark_device_frame (d : Device) (mark : Nat) (net : d.creatingNet = true) :
    Campaign2.Ensures (wgSetDevice (fwmarkAttrs d mark))
      (fun w => w.wg.device = some d ∧ ClaimView.selectsDevice w d)
      (fun ret w => ret = 0 ∧ w.wg.device.map withoutPeers = some
        (withoutPeers { d with fwmark := mark, deviceUpdateGen := d.deviceUpdateGen + 1 })) :=
  setDevice_fwmark_frame d mark net

theorem original_fwmark_clears_listed_peers (d : Device) (mark : Nat) (net : d.creatingNet = true) :
    Campaign2.Ensures (wgSetDevice (fwmarkAttrs d mark))
      (fun w => w.wg.device = some d ∧ ClaimView.selectsDevice w d)
      (fun ret w => ret = 0 ∧ w.wg.device.map withoutPeers = some
        (withoutPeers { d with fwmark := mark, deviceUpdateGen := d.deviceUpdateGen + 1 }) ∧
        ClaimView.sourcesClear w.wg.toCore d.peerList) :=
  setDevice_fwmark_sources d mark net

theorem original_socket_reinit (new4 new6 : Option Nat) (d : Device) :
    Campaign2.Returns (socketReinit new4 new6) (fun w => w.wg.device = some d)
      (fun _ w => w.wg.device = some
        { d with sock4 := new4, sock6 := new6, incomingPort := new4.getD d.incomingPort }) :=
  socketReinit_returns new4 new6 d

theorem original_nonzero_socket_init (port : Nat) (nonzero : port ≠ 0)
    (d : Device) (bound : Bool) (net : d.creatingNet = true) :
    Campaign2.Returns (socketInit port) (fun w => w.wg.device = some d ∧ w.wg.portBound port = bound)
      (fun ret w => if bound || d.sock4 == some port || d.sock6 == some port
        then ret = -EADDRINUSE ∧ w.wg.device = some d
        else ret = 0 ∧ w.wg.device = some
          { d with sock4 := some port, sock6 := some port, incomingPort := port }) :=
  socketInit_nonzero_returns port nonzero d bound net

theorem original_fwmark_peer_store_effects (d : Device) (mark : Nat) (net : d.creatingNet = true) :
    Campaign2.Ensures (wgSetDevice (fwmarkAttrs d mark))
      (fun w => w.wg.device = some d ∧ ClaimView.selectsDevice w d)
      (fun ret w => ret = 0 ∧ w.wg.device.map withoutPeers = some
        (withoutPeers { d with fwmark := mark, deviceUpdateGen := d.deviceUpdateGen + 1 }) ∧
        ClaimView.clearedPeers d w.wg.toCore d.peerList) :=
  setDevice_fwmark_effects d mark net

theorem original_nonzero_port_effects (d : Device) (port : Nat) (nonzero : port ≠ 0)
    (bound : Nat → Bool) :
    Campaign2.Ensures (setPort port) (fun w => w.wg.device = some d ∧ w.wg.portBound = bound)
      (fun ret w => if d.incomingPort = port then ret = 0 ∧ w.wg.device = some d
        else ret = (portOutcome d port bound).1 ∧
          w.wg.device.map withoutPeers = some (withoutPeers (portOutcome d port bound).2) ∧
          ClaimView.clearedPeers d w.wg.toCore d.peerList) :=
  setPort_nonzero_effects d port nonzero bound

theorem original_device_nonzero_port (d : Device) (port : Nat) (nonzero : port ≠ 0)
    (net : d.creatingNet = true) (bound : Nat → Bool) :
    Campaign2.Ensures (wgSetDevice (portAttrs d port))
      (fun w => w.wg.device = some d ∧ ClaimView.selectsDevice w d ∧ w.wg.portBound = bound)
      (fun ret w =>
        let updated := { d with deviceUpdateGen := d.deviceUpdateGen + 1 }
        if d.incomingPort = port then ret = 0 ∧ w.wg.device = some updated
        else ret = (portOutcome updated port bound).1 ∧
          w.wg.device.map withoutPeers = some (withoutPeers (portOutcome updated port bound).2) ∧
          ClaimView.clearedPeers d w.wg.toCore d.peerList) :=
  setDevice_port_nonzero d port nonzero net bound

theorem original_zero_socket_range (d : Device) (net : d.creatingNet = true) :
    Campaign2.Ensures (socketInit 0) (fun w => w.wg.device = some d)
      (fun ret w => ret = 0 ∧ ∃ port,
        LOCAL_PORT_LOW ≤ port ∧ port ≤ LOCAL_PORT_HIGH ∧ w.wg.device = some
          { d with sock4 := some port, sock6 := some port, incomingPort := port }) :=
  socketInit_zero d net

theorem original_zero_socket_record_return (d : Device) (net : d.creatingNet = true)
    (a b c e : UInt8) (rest : List HiddenRecord)
    (free4 : d.sock4 ≠ some (drawnPort a b c e))
    (free6 : d.sock6 ≠ some (drawnPort a b c e)) :
    Campaign2.Returns (socketInit 0)
      (fun w => w.wg.device = some d ∧
        w.ambient.hidden = some (udpDrawRecord a b c e :: rest) ∧ w.wg.portBound (drawnPort a b c e) = false)
      (fun ret w => ret = 0 ∧ w.wg.device = some
        { d with sock4 := some (drawnPort a b c e), sock6 := some (drawnPort a b c e), incomingPort := drawnPort a b c e }) := by
  intro g ambient pre
  obtain ⟨⟨ret, final⟩, after, run, post⟩ :=
    socketInit_zero_record_returns d net a b c e rest free4 free6 g ambient pre
  exact ⟨ret, final, after, run, post⟩

theorem original_zero_port_effects (d : Device) (net : d.creatingNet = true) :
    Campaign2.Ensures (setPort 0) (fun w => w.wg.device = some d)
      (fun ret w => ret = 0 ∧ ClaimView.zeroPortEffects d w) :=
  setPort_zero_effects d net

theorem original_device_zero_port (d : Device) (net : d.creatingNet = true) :
    Campaign2.Ensures (wgSetDevice (portAttrs d 0))
      (fun w => w.wg.device = some d ∧ ClaimView.selectsDevice w d)
      (fun ret w => ret = 0 ∧ ClaimView.zeroPortEffects
        { d with deviceUpdateGen := d.deviceUpdateGen + 1 } w) :=
  setDevice_port_zero d net

theorem original_zero_socket_record_tail (d : Device) (net : d.creatingNet = true)
    (a b c e : UInt8) (rest : List HiddenRecord)
    (free4 : d.sock4 ≠ some (drawnPort a b c e))
    (free6 : d.sock6 ≠ some (drawnPort a b c e)) :
    Campaign2.Returns (socketInit 0)
      (fun w => w.wg.device = some d ∧
        w.ambient.hidden = some (udpDrawRecord a b c e :: rest) ∧ w.wg.portBound (drawnPort a b c e) = false)
      (fun ret w => ret = 0 ∧ w.wg.device = some
        { d with sock4 := some (drawnPort a b c e), sock6 := some (drawnPort a b c e), incomingPort := drawnPort a b c e } ∧
        w.ambient.hidden = some rest) := by
  intro g ambient pre
  obtain ⟨⟨ret, final⟩, after, run, post⟩ :=
    socketInit_zero_record_tail_returns d net a b c e rest free4 free6 g ambient pre
  exact ⟨ret, final, after, run, post⟩

theorem original_zero_socket_collision_stop (d : Device) (a b c e : UInt8)
    (rest : List HiddenRecord) (net : d.creatingNet = true) :
    Campaign2.Observes (socketInit 0)
      (fun w => w.wg.device = some d ∧
        w.ambient.hidden = some (udpDrawRecord a b c e :: rest) ∧
        (w.wg.portBound (drawnPort a b c e) || d.sock4 == some (drawnPort a b c e) ||
          d.sock6 == some (drawnPort a b c e)) = true)
      (fun _ out => ∃ site, out = .error
        (.outsideDomain site "the random port draw collides with a bound port")) := by
  intro g ambient pre
  obtain ⟨site, stopped⟩ := socketInit_zero_collision g ambient d a b c e rest pre.1 net pre.2.1 pre.2.2
  exact ⟨site, by simp only [Campaign2.observeResult, stopped, Except.map]⟩

end Leanux.Proofs.WG.Config.SourceClaims
