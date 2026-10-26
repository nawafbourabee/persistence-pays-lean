import PersistencePays.CouplingTV

/-! The actual maximal coupling measure obtained from a common part and disjoint residuals. -/
namespace PersistencePays.MaximalCoupling
noncomputable section
open MeasureTheory Set
open scoped ENNReal
variable {S : Type*} [MeasurableSpace S]

/-- Place the common mass on the diagonal and couple the residuals independently. -/
def residualCoupling (C L R : Measure S) : Measure (S × S) :=
  C.map (fun x => (x,x)) + (L univ)⁻¹ • L.prod R

theorem residual_mass_eq (P Q C L R : Measure S)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsFiniteMeasure C]
    (hP : C+L=P) (hQ : C+R=Q) : L univ = R univ := by
  apply (ENNReal.add_right_inj (show C univ ≠ ∞ by finiteness)).mp
  simpa only [← Measure.add_apply, hP, hQ, measure_univ]

theorem residualCoupling_fst (C L R : Measure S)
    [IsFiniteMeasure L] [IsFiniteMeasure R] (hm : L univ = R univ) :
    (residualCoupling C L R).fst = C+L := by
  unfold residualCoupling
  rw [Measure.fst_add, Measure.fst_map_prodMk (show Measurable (fun x : S => x) from measurable_id)]
  simp only [Measure.map_id']
  change C + Measure.map Prod.fst ((L univ)⁻¹ • L.prod R) = C+L
  rw [Measure.map_smul, Measure.map_fst_prod, smul_smul, ← hm]
  by_cases hL : L univ = 0
  · have hz : L=0 := Measure.measure_univ_eq_zero.mp hL
    simp [hz]
  · rw [ENNReal.inv_mul_cancel hL (by finiteness), one_smul]

theorem residualCoupling_snd (C L R : Measure S)
    [IsFiniteMeasure L] [IsFiniteMeasure R] (hm : L univ = R univ) :
    (residualCoupling C L R).snd = C+R := by
  unfold residualCoupling
  rw [Measure.snd_add, Measure.snd_map_prodMk (show Measurable (fun x : S => x) from measurable_id)]
  simp only [Measure.map_id']
  change C + Measure.map Prod.snd ((L univ)⁻¹ • L.prod R) = C+R
  rw [Measure.map_smul, Measure.map_snd_prod, smul_smul]
  by_cases hL : L univ = 0
  · have hz : R=0 := Measure.measure_univ_eq_zero.mp (hm.symm.trans hL)
    simp [hz]
  · rw [ENNReal.inv_mul_cancel hL (by finiteness), one_smul]

theorem residualCoupling_isProbabilityMeasure (P Q C L R : Measure S)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    [IsFiniteMeasure C] [IsFiniteMeasure L] [IsFiniteMeasure R]
    (hP : C+L=P) (hQ : C+R=Q) :
    IsProbabilityMeasure (residualCoupling C L R) := by
  constructor
  rw [← Measure.fst_univ, residualCoupling_fst C L R (residual_mass_eq P Q C L R hP hQ), hP]
  exact measure_univ

/-- The residual product has total mass equal to either residual, including zero mass. -/
theorem residual_product_mass (L R : Measure S) [IsFiniteMeasure L] [IsFiniteMeasure R]
    (hm : L univ = R univ) :
    ((L univ)⁻¹ • L.prod R) univ = L univ := by
  rw [Measure.smul_apply, smul_eq_mul, ← univ_prod_univ, Measure.prod_prod, ← hm]
  by_cases hz : L univ = 0
  · simp [hz]
  · rw [← mul_assoc, ENNReal.inv_mul_cancel hz (by finiteness), one_mul]

/-- No mass on the diagonal can contribute to disagreement. -/
theorem residualCoupling_disagreement_le (C L R : Measure S)
    [IsFiniteMeasure L] [IsFiniteMeasure R] (hm : L univ = R univ)
    (hmeas : MeasurableSet {z : S×S | z.1 ≠ z.2}) :
    residualCoupling C L R {z | z.1 ≠ z.2} ≤ L univ := by
  unfold residualCoupling
  rw [Measure.add_apply, Measure.map_apply (show Measurable (fun x : S => (x,x)) from measurable_id.prodMk measurable_id) hmeas]
  have hempty : (fun x : S => (x,x)) ⁻¹' {z : S×S | z.1 ≠ z.2} = ∅ := by ext; simp
  rw [hempty, measure_empty, zero_add]
  exact (measure_mono (subset_univ _)).trans_eq (residual_product_mass L R hm)

/-- Opposite residual supports realize the entire residual mass as one event discrepancy. -/
theorem residual_mass_le_probabilityTV (P Q C L R : Measure S)
    [IsFiniteMeasure P] [IsFiniteMeasure Q]
    [IsFiniteMeasure C] [IsFiniteMeasure L] [IsFiniteMeasure R]
    (hP : C+L=P) (hQ : C+R=Q) (A : Set S) (hA : MeasurableSet A)
    (hL : L Aᶜ=0) (hR : R A=0) : L univ ≤ probabilityTV P Q := by
  have hLA : L A = L univ := by
    have he := measure_add_measure_compl hA (μ := L)
    simpa only [hL, add_zero] using he
  have he : P.real A - Q.real A = L.real univ := by
    rw [← hP, ← hQ, measureReal_add_apply, measureReal_add_apply]
    simp only [Measure.real, hLA, hR, ENNReal.toReal_zero, add_zero]
    ring
  calc
    L univ = ENNReal.ofReal |P.real A-Q.real A| := by
      rw [he, abs_of_nonneg measureReal_nonneg, Measure.real, ENNReal.ofReal_toReal (by finiteness)]
    _ ≤ probabilityTV P Q := le_iSup_of_le A (le_iSup_of_le hA le_rfl)

/-- The constructed measure is a maximal coupling, with literal marginals and exact TV disagreement. -/
theorem residualCoupling_maximal (P Q C L R : Measure S)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    [IsFiniteMeasure C] [IsFiniteMeasure L] [IsFiniteMeasure R]
    (hP : C+L=P) (hQ : C+R=Q) (A : Set S) (hA : MeasurableSet A)
    (hL : L Aᶜ=0) (hR : R A=0)
    (hmeas : MeasurableSet {z : S×S | z.1 ≠ z.2}) :
    (residualCoupling C L R).fst=P ∧ (residualCoupling C L R).snd=Q ∧
    residualCoupling C L R {z | z.1 ≠ z.2}=probabilityTV P Q := by
  have hm := residual_mass_eq P Q C L R hP hQ
  have hf := (residualCoupling_fst C L R hm).trans hP
  have hs := (residualCoupling_snd C L R hm).trans hQ
  refine ⟨hf, hs, le_antisymm ?_ ?_⟩
  · exact (residualCoupling_disagreement_le C L R hm hmeas).trans
      (residual_mass_le_probabilityTV P Q C L R hP hQ A hA hL hR)
  · letI := residualCoupling_isProbabilityMeasure P Q C L R hP hQ
    have hb := coupling_probabilityTV (residualCoupling C L R) Prod.fst Prod.snd
      measurable_fst measurable_snd
    change probabilityTV (residualCoupling C L R).fst (residualCoupling C L R).snd ≤ _ at hb
    simpa only [hf, hs] using hb

end
end PersistencePays.MaximalCoupling
#print axioms PersistencePays.MaximalCoupling.residualCoupling_maximal
