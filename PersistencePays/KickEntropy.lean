import PersistencePays.FiniteEntropyPropagation
import PersistencePays.ConditionalEntropy

/-! Exact changes of actual conditional Gaussian entropy under force kicks. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def kickEquiv (g : E → E) (hg : Measurable g) (s : ℝ) : (E × E) ≃ᵐ (E × E) where
  toFun := kick g s
  invFun := kick g (-s)
  left_inv := kick_inverse g s
  right_inv := by intro z; simpa only [neg_neg] using kick_inverse g (-s) z
  measurable_toFun := (kick_measurePreserving g hg s).measurable
  measurable_invFun := (kick_measurePreserving g hg (-s)).measurable

theorem A1.velocity_entropy_finite {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (hK : klDiv μ (phaseGibbs U) ≠ ∞) :
    conditionalGaussianEntropy μ (stdGaussian E) 0 ≠ ∞ := by
  letI : IsProbabilityMeasure (positionGibbs U) := a.gibbs_isProbabilityMeasure
  have he := klDiv_product_reference_decomposition μ (positionGibbs U) (stdGaussian E)
  change klDiv μ (phaseGibbs U) = _ at he
  simp only [conditionalGaussianEntropy, transportJoint_zero, transportPosition_zero]
  apply ne_top_of_le_ne_top hK
  rw [he]
  exact le_add_left le_rfl

theorem A1.phase_entropy_eq_sum {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (hK : klDiv μ (phaseGibbs U) ≠ ∞) :
    (klDiv μ (phaseGibbs U)).toReal = (klDiv μ.fst (positionGibbs U)).toReal +
      (conditionalGaussianEntropy μ (stdGaussian E) 0).toReal := by
  letI : IsProbabilityMeasure (positionGibbs U) := a.gibbs_isProbabilityMeasure
  have he := klDiv_product_reference_decomposition μ (positionGibbs U) (stdGaussian E)
  change klDiv μ (phaseGibbs U) = _ at he
  have hX : klDiv μ.fst (positionGibbs U) ≠ ∞ := by
    apply ne_top_of_le_ne_top hK
    rw [he]
    exact le_add_right le_rfl
  have hV := a.velocity_entropy_finite μ hK
  simp only [conditionalGaussianEntropy, transportJoint_zero, transportPosition_zero] at hV ⊢
  rw [he, ENNReal.toReal_add hX hV]

theorem map_position_preserving_fst (μ : Measure (E × E))
    (e : (E × E) ≃ᵐ (E × E)) (hfst : ∀ z, (e z).1=z.1) :
    (μ.map e).fst = μ.fst := by
  change (μ.map e).map Prod.fst = μ.map Prod.fst
  rw [Measure.map_map measurable_fst e.measurable]
  congr 1
  funext z
  exact hfst z

/-- Conditional velocity entropy changes exactly by kinetic energy under any
volume-preserving position-preserving map. -/
theorem A1.position_stage_velocity_entropy {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (e : (E × E) ≃ᵐ (E × E))
    (he : MeasurePreserving e ((volume : Measure E).prod volume) ((volume : Measure E).prod volume))
    (hfst : ∀ z, (e z).1=z.1) (hμ : MemLp id 2 μ) (hμe : MemLp e 2 μ)
    (hK : klDiv μ (phaseGibbs U) ≠ ∞) :
    conditionalGaussianEntropy (μ.map e) (stdGaussian E) 0 ≠ ∞ ∧
      (conditionalGaussianEntropy (μ.map e) (stdGaussian E) 0).toReal -
        (conditionalGaussianEntropy μ (stdGaussian E) 0).toReal =
      ∫ z, (kineticPotential (e z).2-kineticPotential z.2) ∂μ := by
  letI : IsProbabilityMeasure (μ.map e) := Measure.isProbabilityMeasure_map e.measurable.aemeasurable
  have hKt := hK
  rw [phaseGibbs_eq_tilted U a.twice_contDiff.continuous.measurable a.gibbs_integrable] at hKt
  have hc := volume_preserving_entropy_change _ (phaseEnergy U)
    (phaseEnergy_measurable U a.twice_contDiff.continuous.measurable)
    (phase_gibbs_integrable U a.gibbs_integrable) μ e he hKt
      ((a.phaseEnergy_integrable hμe).sub (a.phaseEnergy_integrable hμ))
  rw [← phaseGibbs_eq_tilted U a.twice_contDiff.continuous.measurable a.gibbs_integrable] at hc
  refine ⟨a.velocity_entropy_finite _ hc.1, ?_⟩
  have hi := a.phase_entropy_eq_sum μ hK
  have ho := a.phase_entropy_eq_sum (μ.map e) hc.1
  rw [map_position_preserving_fst μ e hfst] at ho
  have henergy : (fun z => phaseEnergy U (e z)-phaseEnergy U z) =
      fun z => kineticPotential (e z).2-kineticPotential z.2 := by
    funext z
    rw [phaseEnergy_eq_norm, phaseEnergy_eq_norm, hfst z]
    dsimp [kineticPotential]
    ring
  rw [henergy] at hc
  linarith [hc.2]

theorem kick_kinetic_change (g : E → E) (s : ℝ) (z : E × E) :
    kineticPotential (kick g s z).2-kineticPotential z.2 =
      -s*⟪z.2,g z.1⟫ + s^2/2*‖g z.1‖^2 := by
  simp only [kineticPotential, kick, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
    real_inner_smul_right, mul_pow, sq_abs]
  ring

/-- The actual kick identity used twice in Lemma 4.9(ii). -/
theorem A1.kick_velocity_entropy {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (s : ℝ) (hμ : MemLp id 2 μ) (hK : klDiv μ (phaseGibbs U) ≠ ∞) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let e := kickEquiv (gradient U) hg s
    conditionalGaussianEntropy (μ.map e) (stdGaussian E) 0 ≠ ∞ ∧
      (conditionalGaussianEntropy (μ.map e) (stdGaussian E) 0).toReal -
        (conditionalGaussianEntropy μ (stdGaussian E) 0).toReal =
      ∫ z, (-s*⟪z.2,gradient U z.1⟫ + s^2/2*‖gradient U z.1‖^2) ∂μ := by
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  have hh := a.position_stage_velocity_entropy μ (kickEquiv (gradient U) hg s)
    (kick_measurePreserving (gradient U) hg s) (fun _ => rfl) hμ (a.kick_memLp hμ s) hK
  simpa only [kickEquiv, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, kick_kinetic_change] using hh

end PersistencePays
#print axioms PersistencePays.A1.kick_velocity_entropy
