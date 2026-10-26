import PersistencePays.GaussianSmoothingEntropy

/-! Actual Gaussian-reference KL convergence for the truncation/Gaussian
approximants used in the nonsmooth free-transport passage. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped ENNReal Topology

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S] [PolishSpace S]

theorem klDiv_toReal_tendsto_of_upper_bound
    (μn : ℕ → ProbabilityMeasure S) (μ γ : ProbabilityMeasure S)
    (hw : Tendsto μn atTop (𝓝 μ))
    (hKn : ∀ n, klDiv (μn n : Measure S) (γ : Measure S) ≠ ∞)
    (hK : klDiv (μ : Measure S) (γ : Measure S) ≠ ∞)
    (b : ℕ → ℝ) (hb : Tendsto b atTop (𝓝 (klDiv (μ : Measure S) (γ : Measure S)).toReal))
    (hbound : ∀ n, (klDiv (μn n : Measure S) (γ : Measure S)).toReal ≤ b n) :
    Tendsto (fun n => (klDiv (μn n : Measure S) (γ : Measure S)).toReal) atTop
      (𝓝 (klDiv (μ : Measure S) (γ : Measure S)).toReal) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact klDiv_toReal_eventually_gt μn μ γ hw hKn hK ha
  · intro a ha
    exact (hb.eventually (gt_mem_nhds ha)).mono (fun n hn => (hbound n).trans_lt hn)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem A1.phaseGaussian_entropy_finite {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    (hK : klDiv μ (phaseGibbs U) ≠ ∞) :
    klDiv μ (gaussianPairProbability (E:=E) : Measure (E×E)) ≠ ∞ := by
  have hh := (gibbs_reference_entropy_change (volume.prod volume : Measure (E×E))
    (phaseEnergy U) (phaseEnergy kineticPotential)
    (phaseEnergy_measurable U a.twice_contDiff.continuous.measurable)
    (phaseEnergy_measurable kineticPotential (by unfold kineticPotential; fun_prop))
    (phase_gibbs_integrable U a.gibbs_integrable)
    (phase_gibbs_integrable kineticPotential kinetic_gibbs_integrable) μ
    ((phaseGaussianEnergy_integrable μ hμ).sub (a.phaseEnergy_integrable hμ))
    (by simpa only [← phaseGibbs_eq_tilted U a.twice_contDiff.continuous.measurable a.gibbs_integrable] using hK)).1
  change klDiv μ ((stdGaussian E).prod (stdGaussian E)) ≠ ∞
  rwa [gaussianPair_eq_tilted]

theorem regularizedGaussian_entropy_finite (μ : ProbabilityMeasure (E×E)) (ε : ℕ → ℝ)
    (hμ : MemLp id 2 (μ : Measure (E×E)))
    (hK : klDiv (μ : Measure (E×E)) (gaussianPairProbability (E:=E) : Measure (E×E)) ≠ ∞)
    (n : ℕ) : klDiv (regularizedProbability μ gaussianPairProbability ε n : Measure (E×E))
      (gaussianPairProbability (E:=E) : Measure (E×E)) ≠ ∞ :=
  (gaussianSmoothing_entropy_bound (ballTruncation μ n) (ε n)
    (memLp_conditionedProbability μ _ _ hμ)
    (conditional_klDiv _ _ hK _ (truncationBall_measurable μ n) (truncationBall_mass_ne_zero μ n)).1).1

theorem regularizedGaussian_entropy_tendsto (μ : ProbabilityMeasure (E×E)) (ε : ℕ → ℝ)
    (hμ : MemLp id 2 (μ : Measure (E×E)))
    (hK : klDiv (μ : Measure (E×E)) (gaussianPairProbability (E:=E) : Measure (E×E)) ≠ ∞)
    (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => (klDiv (regularizedProbability μ gaussianPairProbability ε n : Measure (E×E))
      (gaussianPairProbability (E:=E) : Measure (E×E))).toReal) atTop
      (𝓝 (klDiv (μ : Measure (E×E)) (gaussianPairProbability (E:=E) : Measure (E×E))).toReal) := by
  let b : ℕ → ℝ := fun n =>
    (klDiv (ballTruncation μ n : Measure (E×E)) (gaussianPairProbability (E:=E) : Measure (E×E))).toReal +
      2*(ε n)^2*((∫ z,‖z‖^2 ∂(ballTruncation μ n : Measure (E×E)))+
        (∫ z,‖z‖^2 ∂(gaussianPairProbability (E:=E) : Measure (E×E))))
  apply klDiv_toReal_tendsto_of_upper_bound (regularizedProbability μ gaussianPairProbability ε) μ
    gaussianPairProbability (regularizedProbability_weak μ _ ε hε)
    (regularizedGaussian_entropy_finite μ ε hμ hK) hK b
  · have htr := conditioned_klDiv_tendsto μ gaussianPairProbability (truncationBall μ)
      (truncationBall_measurable μ) (truncationBall_mass_ne_zero μ)
      (Filter.Eventually.of_forall (truncationBall_exhausts μ)) hK
    have hm := ballTruncation_integral_tendsto μ hμ.integrable_norm_pow'
    have he := ((hε.pow 2).const_mul 2).mul (hm.add_const
      (∫ z,‖z‖^2 ∂(gaussianPairProbability (E:=E) : Measure (E×E))))
    have hh := htr.add he
    simpa only [id_eq,b,ballTruncation,zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,zero_mul,add_zero] using hh
  · intro n
    exact (gaussianSmoothing_entropy_bound (ballTruncation μ n) (ε n)
      (memLp_conditionedProbability μ _ _ hμ)
      (conditional_klDiv _ _ hK _ (truncationBall_measurable μ n) (truncationBall_mass_ne_zero μ n)).1).2

end PersistencePays
#print axioms PersistencePays.regularizedGaussian_entropy_tendsto
