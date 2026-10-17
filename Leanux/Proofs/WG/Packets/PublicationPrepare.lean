import Leanux.Proofs.WG.Packets.PublicationCurrent

namespace Leanux.Proofs.WG.PublicationIdentity
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open MaterialOrigin Queues Lifetimes

/-- Whole normal prepare, with the fresh selected decrypt receipt in its
actual journal position. Only successful decryption yields Identity; a DEAD
publication is retained without an authorization assertion. -/
theorem prepare_current_identity (history : List SessionOrigin.Receipt) (w v : WGWorld)
    (ambient ambient' : Ambient) (h t : List (MaterialOrigin.Event RxOrigin.Receipt)) (pid : PeerId)
    (support : CurrentIdentity.Inv history w) (compat : RxCredits.RxCompatible w)
    (hr : runWGPrefix RxOrigin.prepare w ambient h = (.ok ((some pid,v),ambient'),t)) :
    ∃ d id ring, ∃ (r : WGRunWitness (RxPacket × Option RxPacket)), ∃ pre suffix,
      w.dev = some d ∧ d.decryptQueue.consume = (some id,ring) ∧
      r.before = Packets.update w (fun d => {d with decryptQueue := ring}) ∧
      r.ambientBefore = CounterWindow.record ambient .decWorkerConsumed true ∧
      r.Valid (RxOrigin.readDecrypt id) ∧
      runWGPrefix (focusStatePrefix MaterialOrigin.Event.life MaterialOrigin.life? (RxOrigin.readDecryptPrefix id))
        r.before r.ambientBefore h = (.ok ((r.value,r.after),r.ambientAfter),h ++ pre) ∧
      t = h ++ pre ++ [MaterialOrigin.Event.receipt (RxOrigin.Receipt.decrypt id r)] ++ suffix ∧
      ∀ out, r.value.2 = some out → CurrentCertificate history id r out pid v := by
  obtain ⟨d,id,ring,hd,hpop,selectedRun⟩ := prepare_selected w v ambient ambient' h t pid hr
  obtain ⟨r,before,suffix,entry,entryAmbient,valid,read,finishRun,he,success⟩ :=
    selected_receipt id _ v _ ambient' h t pid selectedRun
  let entered := Packets.update w (fun d => {d with decryptQueue := ring})
  have state : r.before.dev = some {d with decryptQueue := ring} := by
    simp [entry,Packets.update,hd]
  have hs : CurrentIdentity.Inv history r.before := by
    intro dev hdev slot k hk hv
    have eq : dev = {d with decryptQueue := ring} := Option.some.inj (hdev.symm.trans state)
    subst dev
    exact support d hd slot k hk hv
  have hc : RxCredits.RxCompatible r.before := by
    intro dev skb pkt hdev hp dev' k hdev' hk
    have eq : dev = {d with decryptQueue := ring} := Option.some.inj (hdev.symm.trans state)
    have eq' : dev' = {d with decryptQueue := ring} := Option.some.inj (hdev'.symm.trans state)
    subst dev; subst dev'
    exact compat d skb pkt hd hp d k hd hk
  obtain ⟨pre,hprefix⟩ := StateAppends.focus MaterialOrigin.Event.life MaterialOrigin.life?
    (RxOrigin.readDecryptPrefix id) entered (CounterWindow.record ambient .decWorkerConsumed true) h
  change (runWGPrefix (focusStatePrefix MaterialOrigin.Event.life MaterialOrigin.life? (RxOrigin.readDecryptPrefix id))
    entered (CounterWindow.record ambient .decWorkerConsumed true) h).2 = h ++ pre at hprefix
  rw [read] at hprefix
  change before = h ++ pre at hprefix
  refine ⟨d,id,ring,r,pre,suffix,hd,hpop,entry,entryAmbient,valid,?_,?_,?_⟩
  · simpa only [entry,entryAmbient,hprefix] using read
  · simpa only [hprefix] using he
  · intro out ho
    exact published_current history id r out pid v ambient' hs hc (success out ho)


end Leanux.Proofs.WG.PublicationIdentity
