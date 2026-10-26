import PersistencePays.Pinsker

/-! Total-variation control by the disagreement event in an actual coupling. -/

namespace PersistencePays
open MeasureTheory Set
open scoped ENNReal symmDiff

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]

/-- No independence is required: both endpoint maps are defined on the same
probability space, and their marginal laws are literal push-forwards. -/
theorem coupling_event_bound (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → S) (hX : Measurable X) (hY : Measurable Y)
    (A : Set S) (hA : MeasurableSet A) :
    |(P.map X).real A - (P.map Y).real A| ≤ P.real {ω | X ω ≠ Y ω} := by
  have hpX : (P.map X).real A = P.real (X ⁻¹' A) := by
    simp only [Measure.real, Measure.map_apply hX hA]
  have hpY : (P.map Y).real A = P.real (Y ⁻¹' A) := by
    simp only [Measure.real, Measure.map_apply hY hA]
  rw [hpX, hpY]
  apply (abs_measureReal_sub_le_measureReal_symmDiff
    (hX hA).nullMeasurableSet (hY hA).nullMeasurableSet).trans
  apply measureReal_mono
  · intro ω hω
    by_contra he
    simp only [mem_ofPred_eq, not_not] at he
    simpa [mem_symmDiff, mem_preimage, he] using hω
  · finiteness

theorem coupling_probabilityTV (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → S) (hX : Measurable X) (hY : Measurable Y) :
    probabilityTV (P.map X) (P.map Y) ≤ P {ω | X ω ≠ Y ω} := by
  apply iSup_le
  intro A
  apply iSup_le
  intro hA
  calc
    ENNReal.ofReal |(P.map X).real A - (P.map Y).real A|
      ≤ ENNReal.ofReal (P.real {ω | X ω ≠ Y ω}) :=
        ENNReal.ofReal_le_ofReal (coupling_event_bound P X Y hX hY A hA)
    _ = _ := ENNReal.ofReal_toReal (by finiteness)

/-- Any proved successful-coupling event yields the same bound. The event may
depend on the whole noise block and may be highly nonlocal. -/
theorem coupling_probabilityTV_of_agree (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → S) (hX : Measurable X) (hY : Measurable Y)
    (B : Set Ω) (hB : ∀ ω ∈ B, X ω = Y ω) :
    probabilityTV (P.map X) (P.map Y) ≤ P Bᶜ := by
  apply (coupling_probabilityTV P X Y hX hY).trans
  apply measure_mono
  intro ω hω
  exact fun hm => hω (hB ω hm)

end PersistencePays

#print axioms PersistencePays.coupling_probabilityTV
