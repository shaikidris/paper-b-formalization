import PaperB.SealedBuild
import PaperB.SealedQuery

namespace PaperB.RamLifecycle

/-- Peak construction storage includes the source, registers, workspace, and
sealed copy. Only the sealed payload is retained. Code, control, and telemetry
are uncharged; no header is modeled. -/
structure Readout where
  constructionOperations : Nat
  peakConstructionWords : Nat
  retainedWords : Nat
  queryOperations : Nat

def phase {bits : Nat} (b : SealedBuild.Observation bits)
    (code : Array (RamProgram.Instr bits 4)) (w : Nat)
    (hw : w ≤ 2 ^ bits) (hi : b.sealedWords.size ≤ 2 ^ bits) :
    SealedQuery.Phase bits :=
  ⟨b.sealedWords, w, hi, hw, code⟩

@[simp] theorem readonly_words {bits : Nat} (b : SealedBuild.Observation bits)
    (code : Array (RamProgram.Instr bits 4)) (w : Nat)
    (hw : w ≤ 2 ^ bits) (hi : b.sealedWords.size ≤ 2 ^ bits) :
    (phase b code w hw hi).input.words = b.sealedWords := rfl

/-- The phase has no source-input slot. With bytecode and capacity fixed,
equal payloads give identical phases, hence identical queries at fixed parameters and fuel. -/
theorem phase_eq_of_payload {bits : Nat} {b b' : SealedBuild.Observation bits}
    (code : Array (RamProgram.Instr bits 4)) (w : Nat) (hw : w ≤ 2 ^ bits)
    (hi : b.sealedWords.size ≤ 2 ^ bits) (hi' : b'.sealedWords.size ≤ 2 ^ bits)
    (h : b.sealedWords = b'.sealedWords) :
    phase b code w hw hi = phase b' code w hw hi' := by
  rcases b with ⟨a, s, c, p, t⟩
  rcases b' with ⟨a', s', c', p', t'⟩
  change a = a' at h
  subst a'
  rfl

private def readout {bits : Nat} (b : SealedBuild.Observation bits)
    (o : SealedQuery.Observation) : Readout :=
  ⟨b.operations, b.peakConstructionWords, b.retainedWords, o.operations⟩

def observe {bits : Nat} (b : SealedBuild.Observation bits)
    (code : Array (RamProgram.Instr bits 4)) (w : Nat) (hw : w ≤ 2 ^ bits)
    (hi : b.sealedWords.size ≤ 2 ^ bits) (q : SealedQuery.Params bits)
    (fuel : Nat) : Option (Bool × Readout) :=
  ((phase b code w hw hi).observe q fuel).map (fun o => (o.answer, readout b o))

theorem payload_fits {bits : Nat} {L : RamProgram.Layout bits}
    {cfg : SealedBuild.SealLayout L} {bc : RamProgram.Program L}
    {words : Array _} {hs : words.size = L.inputCap} {bf : Nat}
    {b : SealedBuild.Observation bits}
    (hb : SealedBuild.build cfg bc words hs bf = some b) :
    b.sealedWords.size ≤ 2 ^ bits := by
  obtain ⟨_, _, _, _, hfit, _⟩ := SealedBuild.build_spec hb
  exact hfit

/-- The construction-state witness comes from `build_spec` for `hb`.
Construction charges initialization and copy; query operations charge initialization. -/
theorem observe_spec {bits : Nat} {L : RamProgram.Layout bits}
    {cfg : SealedBuild.SealLayout L} {bc : RamProgram.Program L}
    {words : Array _} {hs : words.size = L.inputCap} {bf : Nat}
    {b : SealedBuild.Observation bits}
    (hb : SealedBuild.build cfg bc words hs bf = some b)
    {code : Array (RamProgram.Instr bits 4)} {w : Nat} {hw : w ≤ 2 ^ bits}
    {hi : b.sealedWords.size ≤ 2 ^ bits} {q : SealedQuery.Params bits}
    {fuel : Nat} {answer : Bool} {m : Readout}
    (h : observe b code w hw hi q fuel = some (answer, m)) :
    let p := phase b code w hw hi
    ∃ (s : RamProgram.State L) (br : RamProgram.Result L)
      (o : SealedQuery.Observation) (qr : RamProgram.Result p.layout),
      RamProgram.run bc ⟨words, hs⟩ bf s = some br ∧
      p.observe q fuel = some o ∧
      RamProgram.run p.code p.input fuel (p.initialState q) = some qr ∧
      answer = o.answer ∧
      m.constructionOperations = br.executed + L.registerCount + L.workCap + cfg.k ∧
      m.peakConstructionWords = words.size + L.registerCount + L.workCap + cfg.k ∧
      m.retainedWords = b.sealedWords.size ∧
      m.queryOperations = qr.executed + 4 + w := by
  obtain ⟨br, hbr, _, _, _, hsteps, _, hc, hp, ht⟩ := SealedBuild.build_spec hb
  let p := phase b code w hw hi
  change (p.observe q fuel).map (fun o => (o.answer, readout b o)) =
    some (answer, m) at h
  cases hq : p.observe q fuel with
  | none =>
    rw [hq] at h
    cases h
  | some o =>
    have hpair : (o.answer, readout b o) = (answer, m) := by
      rw [hq] at h
      exact Option.some.inj h
    have hm : readout b o = m := congrArg Prod.snd hpair
    subst m
    obtain ⟨qr, hr, he, _, _, _, hop, _, _⟩ := p.observe_counts q fuel hq
    refine ⟨_, br, o, qr, hbr, hq, hr, (congrArg Prod.fst hpair).symm, ?_, hp, ht, ?_⟩
    · exact hc.trans (congrArg (fun n => n + L.registerCount + L.workCap + cfg.k) hsteps)
    · exact hop.trans (congrArg (fun n => n + 4 + w) he)

structure FixedControl where
  setupOperations : Nat
  codeMetadataWords : Nat
  programCounterWords : Nat
  retainedHeaderWords : Nat
  querySetupOperations : Nat
  answerDecodingOperations : Nat

def Readout.chargeFixed (r : Readout) (f : FixedControl) : Readout where
  constructionOperations := r.constructionOperations + f.setupOperations
  peakConstructionWords := r.peakConstructionWords +
    (f.codeMetadataWords + f.programCounterWords + f.retainedHeaderWords)
  retainedWords := r.retainedWords + f.retainedHeaderWords
  queryOperations := r.queryOperations +
    (f.querySetupOperations + f.answerDecodingOperations)

theorem Readout.chargeFixed_le (r : Readout) (f : FixedControl) (a b c d : Nat)
    (ha : r.constructionOperations ≤ a) (hb : r.peakConstructionWords ≤ b)
    (hc : r.retainedWords ≤ c) (hd : r.queryOperations ≤ d) :
    (r.chargeFixed f).constructionOperations ≤ a + f.setupOperations ∧
    (r.chargeFixed f).peakConstructionWords ≤
      b + (f.codeMetadataWords + f.programCounterWords + f.retainedHeaderWords) ∧
    (r.chargeFixed f).retainedWords ≤ c + f.retainedHeaderWords ∧
    (r.chargeFixed f).queryOperations ≤
      d + (f.querySetupOperations + f.answerDecodingOperations) :=
  ⟨Nat.add_le_add_right ha _, Nat.add_le_add_right hb _,
   Nat.add_le_add_right hc _, Nat.add_le_add_right hd _⟩

end PaperB.RamLifecycle
