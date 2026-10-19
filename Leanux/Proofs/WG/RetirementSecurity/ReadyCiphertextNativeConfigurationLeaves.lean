import Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertextNativePeerRemoval

/-! Native peer creation and configuration leaves preserve aligned queued
batches; the actual allocation bound supplies vacancy for the new peer slot. -/
namespace Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertext.Configuration
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity Queues.RxCredits Native

theorem create (key : Key) (psk : Option Key) : Preserves (Coherent locals active) (peerCreate key psk) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have fields := (ProjectedAction.iff_run_ambient _ _ _).mp (OccurrenceCreation.wire key psk) w a result v b run
  have owners := (hoare_iff_run_ambient _ _ _).mp (OccurrenceCreation.contents key psk (txQueueContents w))
    w a result v b ⟨before.1.1.choose_spec.peerSlots,rfl⟩ run
  refine ⟨(hoare_iff_run_ambient _ _ _).mp (OccurrenceCreation.create key psk) w a result v b before.1 run,?_⟩
  apply contents_frame before.2 owners
  funext id
  exact congrFun (congrArg Prod.snd fields) id

theorem allowedip_set (pid : PeerId) (ip : AllowedIpAttrs) : Preserves (Coherent locals active) (setAllowedip pid ip) :=
  coherent_join (OccurrenceConfiguration.allowedip_set pid ip)
    (contents_wire (OccurrenceConfiguration.allowedip_set_contents pid ip) (OccurrenceConfiguration.allowedip_set_wire pid ip))

theorem socket_init (port : Nat) : Preserves (Coherent locals active) (socketInit port) :=
  coherent_join (OccurrenceConfiguration.socket_init port)
    (contents_wire (OccurrenceConfiguration.socket_contents (socketInit_sameSocket port))
      (OccurrenceConfiguration.socket_wire (socketInit_sameSocket port)))

theorem socket_reinit (new4 new6 : Option Nat) : Preserves (Coherent locals active) (socketReinit new4 new6) :=
  coherent_join (OccurrenceConfiguration.socket_reinit new4 new6)
    (contents_wire (OccurrenceConfiguration.socket_contents (socketReinit_sameSocket new4 new6))
      (OccurrenceConfiguration.socket_wire (socketReinit_sameSocket new4 new6)))

theorem set_port (port : Nat) : Preserves (Coherent locals active) (setPort port) := by
  unfold setPort
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head clearPeerEndpointSrc; exact clear_endpoint _)
    | (rx_retention_head socketInit; exact socket_init _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Coherent locals active)
       intro x b
       change Preserves (Coherent locals active) _)
    | ready_ciphertext_coherent_step

end Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertext.Configuration
