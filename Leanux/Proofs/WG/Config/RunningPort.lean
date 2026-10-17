import Leanux.Proofs.WG.Config.OperationFrames
import Leanux.Proofs.WG.Config.FwmarkEffects
import Leanux.Proofs.WG.Config.SocketPorts

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def portClearLoop (pids : List PeerId) : WG.M Unit := do
  for pid in pids do
    _ ← branch .setPortPeerIter true
    clearPeerEndpointSrc pid

theorem portClearLoop_effects (initial : Device) (pids seen : List PeerId)
    (frame : Option Device) (bound : Nat → Bool) :
    Ensures (portClearLoop pids)
      (fun w => w.dev.map withoutPeers = frame ∧ clearedPeers initial w seen ∧ w.portBound = bound)
      (fun _ w => w.dev.map withoutPeers = frame ∧
        clearedPeers initial w (seen ++ pids) ∧ w.portBound = bound) := by
  induction pids generalizing seen with
  | nil =>
    intro g ambient result final after pre run
    cases run
    simpa using pre
  | cons pid rest ih =>
    have factor : portClearLoop (pid :: rest) = (do
        _ ← branch .setPortPeerIter true
        clearPeerEndpointSrc pid
        portClearLoop rest) := by
      simp [portClearLoop, List.forIn_cons, bind_assoc]
    have hc : Ensures (clearPeerEndpointSrc pid)
        (fun g => g.dev.map withoutPeers = frame ∧ clearedPeers initial g seen ∧ g.portBound = bound)
        (fun _ g => g.dev.map withoutPeers = frame ∧ clearedPeers initial g (seen ++ [pid]) ∧ g.portBound = bound) := by
      intro g ambient result final after pre run
      obtain ⟨hf, he⟩ := (ensures_iff _ _ _).mpr
        (clearEndpointSource_effects_frame initial pid seen frame) g ambient result final after ⟨pre.1, pre.2.1⟩ run
      exact ⟨hf, he, clearEndpointSource_portBound pid bound g ambient result final after pre.2.2 run⟩
    rw [factor]
    refine ensures_bind (Q := fun _ g => g.dev.map withoutPeers = frame ∧ clearedPeers initial g seen ∧ g.portBound = bound) _ _ ?_ ?_
    · exact (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch .setPortPeerIter true) _)
    · intro _
      refine ensures_bind _ _ hc ?_
      intro _ g ambient result final after pre run
      simpa only [List.append_assoc, List.singleton_append] using
        ih (seen ++ [pid]) g ambient result final after pre run

def socketOutcome (d : Device) (port : Nat) (bound : Nat → Bool) : Int × Device :=
  if !d.creatingNet then (-ENONET, d)
  else if bound port || d.sock4 == some port || d.sock6 == some port then (-EADDRINUSE, d)
  else (0, { d with sock4 := some port, sock6 := some port, incomingPort := port })

theorem socketInit_nonzero_projected (d initial : Device) (seen : List PeerId)
    (port : Nat) (nonzero : port ≠ 0) (bound : Nat → Bool) :
    ⦃fun w => ⌜w.dev.map withoutPeers = some (withoutPeers d) ∧
      clearedPeers initial w seen ∧ w.portBound = bound⌝⦄ socketInit port
    ⦃⇓? ret w => ⌜ret = (socketOutcome d port bound).1 ∧
      w.dev.map withoutPeers = some (withoutPeers (socketOutcome d port bound).2) ∧
      clearedPeers initial w seen⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  obtain ⟨current, device, frame⟩ := Option.map_eq_some_iff.mp pre.1
  have net := congrArg Device.creatingNet frame
  have sock4 := congrArg Device.sock4 frame
  have sock6 := congrArg Device.sock6 frame
  change current.creatingNet = d.creatingNet at net
  change current.sock4 = d.sock4 at sock4
  change current.sock6 = d.sock6 at sock6
  have post : result = (socketOutcome current port bound).1 ∧
      final.dev = some (socketOutcome current port bound).2 := by
    cases hasNet : current.creatingNet with
    | false =>
      simp [socketInit, getDev, device, hasNet] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      simpa [socketOutcome, hasNet] using device
    | true =>
      obtain ⟨ret, out, tail, execution, effects⟩ :=
        socketInit_nonzero_returns port nonzero current (bound port) hasNet
          g ambient ⟨device, congrFun pre.2.2 port⟩
      rw [run] at execution
      cases execution
      cases held : bound port || current.sock4 == some port || current.sock6 == some port <;>
        simpa [socketOutcome, hasNet, held] using effects
  have changedFrame : withoutPeers {current with sock4 := some port, sock6 := some port, incomingPort := port} =
      withoutPeers {d with sock4 := some port, sock6 := some port, incomingPort := port} := by
    exact congrArg
      (fun state : Device => {state with sock4 := some port, sock6 := some port, incomingPort := port}) frame
  have outcomes : (socketOutcome current port bound).1 = (socketOutcome d port bound).1 ∧
      withoutPeers (socketOutcome current port bound).2 = withoutPeers (socketOutcome d port bound).2 := by
    simp only [socketOutcome, net, sock4, sock6]
    split
    · exact ⟨rfl, frame⟩
    · split
      · exact ⟨rfl, frame⟩
      · exact ⟨rfl, by simpa only [net] using changedFrame⟩
  refine ⟨post.1.trans outcomes.1, by simpa [post.2] using congrArg some outcomes.2, ?_⟩
  have clear := pre.2.1
  cases hasNet : current.creatingNet <;>
    cases held : bound port || current.sock4 == some port || current.sock6 == some port <;>
    simpa [clearedPeers, post.2, socketOutcome, hasNet, held, device] using clear

def setPortSource (port : Nat) : WG.M Int := do
  let d ← getDev
  if ← branch .setPortSame (d.incomingPort == port) then return 0
  portClearLoop d.peerList
  _ ← branch .setPortPeerIter false
  if ← branch .setPortNotRunning !d.running then
    modifyDev fun d => { d with incomingPort := port }
    return 0
  socketInit port

theorem setPort_source (port : Nat) : setPortSource port = setPort port := by
  simp [setPortSource, setPort, portClearLoop]

def portOutcome (d : Device) (port : Nat) (bound : Nat → Bool) : Int × Device :=
  if !d.running then (0, { d with incomingPort := port })
  else socketOutcome d port bound

theorem setPort_nonzero_effects (d : Device) (port : Nat) (nonzero : port ≠ 0)
    (bound : Nat → Bool) :
    Ensures (setPort port) (fun w => w.dev = some d ∧ w.portBound = bound)
      (fun ret w => if d.incomingPort = port then ret = 0 ∧ w.dev = some d
        else ret = (portOutcome d port bound).1 ∧
          w.dev.map withoutPeers = some (withoutPeers (portOutcome d port bound).2) ∧
          clearedPeers d w d.peerList) := by
  let Q : WGWorld → Prop := fun g => g.dev.map withoutPeers = some (withoutPeers d) ∧
    clearedPeers d g d.peerList ∧ g.portBound = bound
  let R : Int → WGWorld → Prop := fun ret g => ret = (portOutcome d port bound).1 ∧
    g.dev.map withoutPeers = some (withoutPeers (portOutcome d port bound).2) ∧ clearedPeers d g d.peerList
  let tail : WG.M Int := do
    _ ← branch .setPortPeerIter false
    if ← branch .setPortNotRunning !d.running then
      modifyDev fun d => {d with incomingPort := port}
      return 0
    socketInit port
  have ht : Ensures tail Q R := by
    unfold tail
    refine ensures_bind (Q := fun _ => Q) _ _ ?_ ?_
    · exact (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch .setPortPeerIter false) _)
    · intro _
      refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (branch_state_spec Q .setPortNotRunning (!d.running))) ?_
      intro decision g ambient result final after pre run
      obtain ⟨rfl, pre⟩ := pre
      cases running : d.running with
      | false =>
        simp only [running, Bool.not_false, ite_true] at run
        simp [modifyDev] at run
        rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
        obtain ⟨current, device, frame⟩ := Option.map_eq_some_iff.mp pre.1
        have changedFrame : withoutPeers {current with incomingPort := port} = withoutPeers {d with incomingPort := port} := by
          exact congrArg (fun state : Device => {state with incomingPort := port}) frame
        refine ⟨by simp [portOutcome, running], ?_, ?_⟩
        · simpa [R, portOutcome, running, device] using congrArg some changedFrame
        · simpa [clearedPeers, device] using pre.2.1
      | true =>
        have result := (ensures_iff _ _ _).mpr
          (socketInit_nonzero_projected d d d.peerList port nonzero bound)
          g ambient result final after pre (by simpa only [running, Bool.not_true, Bool.false_eq_true, ite_false] using run)
        simpa [R, portOutcome, running] using result
  intro g ambient result final after pre run
  by_cases same : d.incomingPort = port
  · simp [setPort, getDev, pre.1, branch, AmbientM.branch, same] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    simp [same, pre.1]
  · have different : (d.incomingPort == port) = false := by simp [same]
    let before := {ambient with steps := ambient.steps.push {
      decision := .setPortSame, outcome := false, netRx := ambient.netRxSection}}
    have source : ((setPort port).run g).run ambient =
        (((do portClearLoop d.peerList; tail) : WG.M Int).run g).run before := by
      rw [← setPort_source]
      simp [setPortSource, getDev, pre.1, branch, AmbientM.branch, same, different, tail, before]
    have whole : Ensures (do portClearLoop d.peerList; tail)
        (fun g => g.dev.map withoutPeers = some (withoutPeers d) ∧ clearedPeers d g [] ∧ g.portBound = bound) R := by
      refine ensures_bind _ _ (portClearLoop_effects d d.peerList [] _ bound) ?_
      intro _
      exact ht
    have post := whole g before result final after (by simp [clearedPeers, pre.1, pre.2]) (source.symm.trans run)
    simpa [same, R] using post

end Leanux.Proofs.WG.Config
