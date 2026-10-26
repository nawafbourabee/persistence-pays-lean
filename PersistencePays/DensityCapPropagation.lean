import PersistencePays.FiniteEntropyPropagation
import PersistencePays.WarmStart

/-! Lebesgue density caps for the actual Gaussian/volume comparison chain. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

section Mixture
variable {S B T : Type*} [MeasurableSpace S] [MeasurableSpace B] [MeasurableSpace T]

theorem mixture_map_constant (ξ : Measure S) [SFinite ξ]
    (ν : Measure B) [IsProbabilityMeasure ν] (ζ : Measure T)
    (f : S × B → T) (hf : Measurable f)
    (hmap : ∀ b, ξ.map (fun x => f (x,b)) = ζ) :
    (ξ.prod ν).map f = ζ := by
  ext A hA
  let F : S × B → ℝ≥0∞ := fun p => A.indicator (fun _ => 1) (f p)
  have hF : Measurable F := (measurable_const.indicator hA).comp hf
  calc
    (ξ.prod ν).map f A = ∫⁻ p, F p ∂ξ.prod ν := by
      rw [← lintegral_map (measurable_const.indicator hA) hf]
      rw [lintegral_indicator hA]
      simp
    _ = ∫⁻ b, ∫⁻ x, F (x,b) ∂ξ ∂ν := by
      rw [lintegral_prod _ hF.aemeasurable, lintegral_lintegral_swap hF.aemeasurable]
    _ = ∫⁻ _ : B, ζ A ∂ν := by
      apply lintegral_congr
      intro b
      have hm : Measurable (fun x => f (x,b)) := hf.comp (measurable_id.prodMk measurable_const)
      change (∫⁻ x, A.indicator (fun _ => 1) (f (x,b)) ∂ξ) = _
      rw [← lintegral_map (measurable_const.indicator hA) hm, hmap b]
      rw [lintegral_indicator hA]
      simp
    _ = ζ A := by simp
end Mixture

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def ouVolumeFactor (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (|r⁻¹| ^ Module.finrank ℝ E)

theorem ou_fixed_noise_volume (r σ : ℝ) (hr : r ≠ 0) (ξ : E) :
    ((volume : Measure E).prod volume).map (OBABOPath.ou r σ ξ) =
      ouVolumeFactor (E := E) r • ((volume : Measure E).prod volume) := by
  have hv : (volume : Measure E).map (fun v => r • v + σ • ξ) =
      ouVolumeFactor (E := E) r • volume := by
    change Measure.map ((fun v : E => v+σ•ξ) ∘ (fun v : E => r•v)) volume = _
    rw [← Measure.map_map (by fun_prop) (by fun_prop), Measure.map_addHaar_smul volume hr,
      Measure.map_smul, (measurePreserving_add_right volume (σ•ξ)).map_eq]
    simp [ouVolumeFactor, ← inv_pow, abs_pow]
  change Measure.map (Prod.map (id : E → E) (fun v => r•v+σ•ξ)) (volume.prod volume) = _
  rw [← Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_id, hv,
    Measure.prod_smul_right]

theorem phaseOUKernel_volume (r σ : ℝ) (hr : r ≠ 0) :
    phaseOUKernel r σ ∘ₘ ((volume : Measure E).prod volume) =
      ouVolumeFactor (E := E) r • ((volume : Measure E).prod volume) := by
  rw [phaseOUKernel_comp_map]
  exact mixture_map_constant _ _ _ (fun p => OBABOPath.ou r σ p.2 p.1)
    (by unfold OBABOPath.ou; fun_prop) (fun ξ => ou_fixed_noise_volume r σ hr ξ)

theorem phaseOUKernel_density_cap (μ : Measure (E × E)) (C : ℝ≥0∞)
    (hμ : μ ≤ C • ((volume : Measure E).prod volume)) (r σ : ℝ) (hr : r ≠ 0) :
    phaseOUKernel r σ ∘ₘ μ ≤
      (C*ouVolumeFactor (E := E) r) • ((volume : Measure E).prod volume) := by
  have hh := kernel_comp_mono (phaseOUKernel r σ) hμ
  rw [Measure.comp_smul, phaseOUKernel_volume r σ hr, smul_smul] at hh
  exact hh

theorem volume_stage_density_cap (μ : Measure (E × E)) (C : ℝ≥0∞)
    (hμ : μ ≤ C • ((volume : Measure E).prod volume))
    (D : E × E → E × E)
    (hD : MeasurePreserving D ((volume : Measure E).prod volume) ((volume : Measure E).prod volume)) :
    μ.map D ≤ C • ((volume : Measure E).prod volume) := by
  have hh : μ.map D ≤ (C • ((volume : Measure E).prod volume)).map D := Measure.map_mono hμ hD.measurable
  rw [Measure.map_smul, hD.map_eq] at hh
  exact hh

theorem gaussianSandwichKernel_density_cap (μ : Measure (E × E)) [SFinite μ]
    (C : ℝ≥0∞) (hμ : μ ≤ C • ((volume : Measure E).prod volume))
    (D : E × E → E × E)
    (hD : MeasurePreserving D ((volume : Measure E).prod volume) ((volume : Measure E).prod volume))
    (r σ : ℝ) (hr : r ≠ 0) :
    gaussianSandwichKernel D hD.measurable r σ ∘ₘ μ ≤
      (C*ouVolumeFactor (E := E) r^2) • ((volume : Measure E).prod volume) := by
  rw [gaussianSandwichKernel_comp]
  have hh := phaseOUKernel_density_cap _ _
    (volume_stage_density_cap _ _ (phaseOUKernel_density_cap μ C hμ r σ hr) D hD) r σ hr
  simpa only [pow_two, mul_assoc] using hh

theorem gaussianSandwichKernel_iterates_density_cap (μ : Measure (E × E)) [SFinite μ]
    (C : ℝ≥0∞) (hμ : μ ≤ C • ((volume : Measure E).prod volume))
    (D : E × E → E × E)
    (hD : MeasurePreserving D ((volume : Measure E).prod volume) ((volume : Measure E).prod volume))
    (r σ : ℝ) (hr : r ≠ 0) (n : ℕ) :
    iterateKernel (gaussianSandwichKernel D hD.measurable r σ) n ∘ₘ μ ≤
      (C*(ouVolumeFactor (E := E) r^2)^n) • ((volume : Measure E).prod volume) := by
  induction n with
  | zero => simpa only [iterateKernel, Measure.id_comp, pow_zero, mul_one] using hμ
  | succ n ih =>
    rw [iterateKernel, ← Measure.comp_assoc]
    have hb := gaussianSandwichKernel_density_cap _ _ ih D hD r σ hr
    simpa only [pow_succ, mul_assoc] using hb


theorem obabo_step_measure_cap (g : E → E) (hg : Measurable g)
    (h r σ : ℝ) (hh : 0 < h) (hσ : 0 < σ) (z : E × E) :
    OBABOPath.unadjustedStepKernel g hg h r σ z ≤
      ENNReal.ofReal (((2*Real.pi*h*σ^2)^Module.finrank ℝ E)⁻¹) •
        ((volume : Measure E).prod volume) := by
  obtain ⟨f, _, he, hf⟩ := obabo_step_density_bound g hg h r σ hh hσ z
  rw [he, ← withDensity_const]
  exact withDensity_mono (Filter.Eventually.of_forall hf)

theorem ouVolumeFactor_exp (t : ℝ) :
    ouVolumeFactor (E := E) (Real.exp (-t)) =
      ENNReal.ofReal (Real.exp ((Module.finrank ℝ E : ℝ)*t)) := by
  unfold ouVolumeFactor
  rw [Real.exp_neg, inv_inv, abs_of_pos (Real.exp_pos t), Real.exp_nat_mul]

/-- Every measure dominated by a constant multiple of Lebesgue measure has
an actual measurable density bounded everywhere by that constant. -/
theorem exists_density_of_measure_cap {S : Type*} [MeasurableSpace S]
    (μ ξ : Measure S) [IsFiniteMeasure μ] [SigmaFinite ξ] (C : ℝ≥0∞)
    (hμ : μ ≤ C • ξ) :
    ∃ f : S → ℝ≥0∞, Measurable f ∧ μ = ξ.withDensity f ∧ ∀ x, f x ≤ C := by
  have ha : μ ≪ ξ := by
    intro A hA
    apply le_antisymm _ bot_le
    simpa [Measure.smul_apply, hA] using hμ A
  have hRN : μ.rnDeriv ξ ≤ᵐ[ξ] fun _ => C := by
    refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite (μ.measurable_rnDeriv ξ) ?_
    intro A _ _
    have hb := (Measure.setLIntegral_rnDeriv_le (μ := μ) (ν := ξ) A).trans (hμ A)
    simpa only [lintegral_const, Measure.restrict_apply_univ, Measure.smul_apply, smul_eq_mul] using hb
  refine ⟨fun x => min (μ.rnDeriv ξ x) C, (μ.measurable_rnDeriv ξ).min measurable_const, ?_, fun _ => min_le_right _ _⟩
  calc
    μ = ξ.withDensity (μ.rnDeriv ξ) := (Measure.withDensity_rnDeriv_eq μ ξ ha).symm
    _ = _ := by
      apply withDensity_congr_ae
      filter_upwards [hRN] with x hx
      exact (min_eq_left hx).symm

/-- Starting from the actual first unadjusted step, the comparison chain's
pre-Hamiltonian law has precisely the cap needed in Lemma 5.11. -/
theorem comparison_pre_step_density_cap (g : E → E) (hg : Measurable g)
    (h σ vstar : ℝ) (hh : 0 < h) (hσ : 0 < σ) (z : E × E) (n : ℕ) :
    let r := Real.exp (-h)
    let e := comparisonVerletEquiv g hg h vstar
    let P := gaussianSandwichKernel e e.measurable r σ
    let μ₁ := OBABOPath.unadjustedStepKernel g hg h r σ z
    let μ := phaseOUKernel r σ ∘ₘ (iterateKernel P n ∘ₘ μ₁)
    ∃ f : E × E → ℝ≥0∞, Measurable f ∧ μ = ((volume : Measure E).prod volume).withDensity f ∧
      ∀ w, f w ≤ ENNReal.ofReal ((((2*Real.pi*h*σ^2)^Module.finrank ℝ E)⁻¹) *
        Real.exp ((2*(n:ℝ)+1)*(Module.finrank ℝ E : ℝ)*h)) := by
  let r := Real.exp (-h)
  let e := comparisonVerletEquiv g hg h vstar
  let P := gaussianSandwichKernel e e.measurable r σ
  let μ₁ := OBABOPath.unadjustedStepKernel g hg h r σ z
  let C := ENNReal.ofReal (((2*Real.pi*h*σ^2)^Module.finrank ℝ E)⁻¹)
  have hi : μ₁ ≤ C • ((volume : Measure E).prod volume) := obabo_step_measure_cap g hg h r σ hh hσ z
  have hb := gaussianSandwichKernel_iterates_density_cap μ₁ C hi e
    (comparisonVerlet_measurePreserving g hg h vstar) r σ (Real.exp_ne_zero _) n
  have hpre := phaseOUKernel_density_cap _ _ hb r σ (Real.exp_ne_zero _)
  change phaseOUKernel r σ ∘ₘ (iterateKernel P n ∘ₘ μ₁) ≤
    ((C*(ouVolumeFactor (E := E) r^2)^n)*ouVolumeFactor (E := E) r) • _ at hpre
  have hc : (C*(ouVolumeFactor (E := E) r^2)^n)*ouVolumeFactor (E := E) r =
      ENNReal.ofReal ((((2*Real.pi*h*σ^2)^Module.finrank ℝ E)⁻¹) *
        Real.exp ((2*(n:ℝ)+1)*(Module.finrank ℝ E : ℝ)*h)) := by
    dsimp [C, r]
    rw [ouVolumeFactor_exp, ← ENNReal.ofReal_pow (Real.exp_nonneg _),
      ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
    congr 2
    push_cast
    ring
  rw [hc] at hpre
  exact exists_density_of_measure_cap _ _ _ hpre


/-- The uniform epoch cap displayed in Lemma 5.11; index `n` corresponds to
`W_{n+1}` after the first unadjusted step. -/
theorem lemma_5_11_density (g : E → E) (hg : Measurable g)
    (h σ vstar : ℝ) (hh : 0 < h) (hσ : 0 < σ) (z : E × E)
    (n N : ℕ) (hn : n+1 ≤ N) :
    let r := Real.exp (-h)
    let e := comparisonVerletEquiv g hg h vstar
    let P := gaussianSandwichKernel e e.measurable r σ
    let μ₁ := OBABOPath.unadjustedStepKernel g hg h r σ z
    let μ := phaseOUKernel r σ ∘ₘ (iterateKernel P n ∘ₘ μ₁)
    ∃ f : E × E → ℝ≥0∞, Measurable f ∧ μ = ((volume : Measure E).prod volume).withDensity f ∧
      ∀ w, f w ≤ ENNReal.ofReal ((((2*Real.pi*h*σ^2)^Module.finrank ℝ E)⁻¹) *
        Real.exp (2*(Module.finrank ℝ E : ℝ)*((N:ℝ)*h))) := by
  obtain ⟨f, hf, he, hb⟩ := comparison_pre_step_density_cap g hg h σ vstar hh hσ z n
  refine ⟨f, hf, he, fun w => (hb w).trans ?_⟩
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hn' : (n:ℝ)+1 ≤ (N:ℝ) := by exact_mod_cast hn
  have hd : 0 ≤ (Module.finrank ℝ E : ℝ)*h := by positivity
  nlinarith

end PersistencePays
#print axioms PersistencePays.phaseOUKernel_volume
#print axioms PersistencePays.gaussianSandwichKernel_iterates_density_cap

#print axioms PersistencePays.comparison_pre_step_density_cap

#print axioms PersistencePays.lemma_5_11_density
