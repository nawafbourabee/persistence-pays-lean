import PersistencePays.ExceptionalMoment
import PersistencePays.ComparisonChainBounds
import PersistencePays.ComparisonMomentIteration

/-! First energy moment for the actual capped comparison chain, using
agreement on the stopped event and the checked fourth-moment bound. -/
noncomputable section
namespace PersistencePays.OBABOPath
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem comparison_energy_exceptional
    {U : E → ℝ} {L LH h vstar R : ℝ} (a : A1 U 1 L) (a2 : A2 U LH)
    (hstar : a.minimizer = 0) (hzero : U 0 = 0)
    (hh : 0 ≤ h) (hL : h^2*L ≤ 1/64)
    (hv : 0 ≤ vstar) (hLH : 0 ≤ LH)
    (hscale : LH*h^3/12*vstar ≤ (0.02:ℝ)*h)
    (hR : 0 ≤ R) (z : E × E) (hz : phaseEnergy U z ≤ R) (n : ℕ) :
    let r := Real.exp (-h)
    let σ := Real.sqrt (1-Real.exp (-2*h))
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let μ := comparisonChainLaw (gradient U) hg h r σ vstar n z
    let Q := (1.2:ℝ)*R+27*(Module.finrank ℝ E : ℝ)+50
    (∫ w, phaseEnergy U w ∂μ) ≤ (1.266:ℝ)*Q +
      (1.005:ℝ)*secondMomentNorm μ (modifiedEnergy U h)*
        Real.sqrt ((gaussianBlock (n+1)).real
          (stoppedBlockEvent U (gradient U) h r σ vstar (n+1) z)ᶜ) := by
  dsimp only
  let r := Real.exp (-h)
  let σ := Real.sqrt (1-Real.exp (-2*h))
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let μ := comparisonChainLaw (gradient U) hg h r σ vstar n z
  let C : NoiseBlock E (n+1) → E×E := fun b =>
    comparisonEndpoint (gradient U) h r σ vstar (n+1) (z,b)
  let A := stoppedBlockEvent U (gradient U) h r σ vstar (n+1) z
  let F : NoiseBlock E (n+1) → ℝ := fun b => phaseEnergy U (C b)
  let G : NoiseBlock E (n+1) → ℝ := fun b => modifiedEnergy U h (C b)
  let H : NoiseBlock E (n+1) → ℝ := fun b =>
    phaseEnergy U (unadjustedEpochEndpoint (gradient U) h r σ (n+1) (z,b))
  have hC : Measurable C := (measurable_comparisonEndpoint (gradient U) hg h r σ vstar
    (n+1)).comp measurable_prodMk_left
  have hmap : (gaussianBlock (n+1)).map C = μ := comparison_endpoint_law (gradient U) hg h r σ vstar n z
  have hμ4 : MemLp id 4 μ := comparisonChainLaw_finite_moments a h r σ vstar n z 4 (by norm_num)
  have hGμ : MemLp (modifiedEnergy U h) 2 μ := a.modifiedEnergy_memLp_two hstar hzero hL μ hμ4
  have hG : MemLp G 2 (gaussianBlock (n+1)) := by
    apply (memLp_map_measure_iff (a.modifiedEnergy_measurable h).aestronglyMeasurable hC.aemeasurable).mp
    rwa [hmap]
  have hU := a.twice_contDiff.continuous.measurable
  have hH : Measurable (phaseEnergy U) := by unfold phaseEnergy; fun_prop
  have hF : Measurable F := hH.comp hC
  have hF0 (b : NoiseBlock E (n+1)) : 0 ≤ F b := a.normalized_energy_nonnegative hstar hzero (C b)
  have hG0 (b : NoiseBlock E (n+1)) : 0 ≤ G b := a.modifiedEnergy_nonnegative hstar hzero hL (C b)
  have hbound (b : NoiseBlock E (n+1)) : F b ≤ (1.005:ℝ)*G b := by
    have ht := (lyapunov_energy_bounds a hstar hzero hL (C b)).2.2.1
    change (0.996:ℝ)*F b ≤ G b at ht
    nlinarith [hF0 b]
  have hr : r^2 ≤ 1 := by
    have hc := normalized_ou_coefficients h hh
    have he : r^2+σ^2=1 := hc.2.2.2.1
    nlinarith [sq_nonneg σ]
  have hagree (b : NoiseBlock E (n+1)) (hb : b ∈ A) : F b = H b :=
    congrArg (phaseEnergy U) (comparison_agree_on_stoppedBlock a hstar hzero hL hr hv
      (n+1) z b hb (n+1) le_rfl)
  have ht := exceptional_event_expectation (gaussianBlock (n+1)) F G H hF hG hF0 hG0
    (1.005:ℝ) (by norm_num) hbound A (stoppedBlockEvent_measurable a h r σ vstar (n+1) z) hagree
  have hfirst : (∫ b in A, H b ∂gaussianBlock (n+1)) ≤
      (1.266:ℝ)*((1.2:ℝ)*R+27*(Module.finrank ℝ E : ℝ)+50) := by
    have hs := (stopped_path_energy_moment a a2 hstar hzero hh hL hv hLH hscale hR z hz
      (n+1) 1 (by norm_num) (by norm_num)).2
    simpa only [Real.rpow_one] using hs
  have heF : (∫ b, F b ∂gaussianBlock (n+1)) = ∫ w, phaseEnergy U w ∂μ := by
    rw [← hmap, integral_map hC.aemeasurable hH.aestronglyMeasurable]
  have heG : secondMomentNorm (gaussianBlock (n+1)) G = secondMomentNorm μ (modifiedEnergy U h) := by
    unfold secondMomentNorm
    rw [← hmap, integral_map hC.aemeasurable
      ((a.modifiedEnergy_measurable h).pow_const 2).aestronglyMeasurable]
  rw [heF, heG] at ht
  exact ht.trans (add_le_add hfirst le_rfl)

end PersistencePays.OBABOPath
#print axioms PersistencePays.OBABOPath.comparison_energy_exceptional
