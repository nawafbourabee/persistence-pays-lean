import PersistencePays.TransportGluing

/-! Genuine quadratic Wasserstein distance and its gluing-based triangle inequality. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem sqrt_integral_norm_add_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f g : Ω → E}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Real.sqrt (∫ x, ‖f x+g x‖^2 ∂μ) ≤
      Real.sqrt (∫ x, ‖f x‖^2 ∂μ)+Real.sqrt (∫ x, ‖g x‖^2 ∂μ) := by
  have hinner := integrable_inner_of_memLp_two hf hg
  have hc := abs_integral_inner_le_sqrt hf hg
  have h1 := Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg ‖f x‖) (μ := μ))
  have h2 := Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg ‖g x‖) (μ := μ))
  have he : (∫ x, ‖f x+g x‖^2 ∂μ) = (∫ x, ‖f x‖^2 ∂μ)+
      2*(∫ x, ⟪f x,g x⟫ ∂μ)+(∫ x, ‖g x‖^2 ∂μ) := by
    simp_rw [norm_add_sq_real]
    have hi : Integrable (fun x => ‖f x‖^2+2*⟪f x,g x⟫) μ :=
      hf.integrable_norm_pow'.add (hinner.const_mul 2)
    rw [integral_add hi hg.integrable_norm_pow',
      integral_add hf.integrable_norm_pow' (hinner.const_mul 2), integral_const_mul]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity,?_⟩
  rw [he]
  have hn := le_abs_self (∫ x, ⟪f x,g x⟫ ∂μ)
  nlinarith

namespace QuadraticTransport

def wassersteinTwo (μ ν : ProbabilityMeasure E) : ℝ := Real.sqrt (cost μ ν).toReal

theorem squaredCost_toReal (μ ν : ProbabilityMeasure E) (π : ProbabilityMeasure (E × E))
    (hπ : π ∈ plans μ ν) (hμ : MemLp id 2 (μ : Measure E)) (hν : MemLp id 2 (ν : Measure E)) :
    (squaredCost π).toReal = ∫ z, ‖z.1-z.2‖^2 ∂(π : Measure (E × E)) := by
  exact (integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    (squaredCost_integrable μ ν π hπ hμ.integrable_norm_pow' hν.integrable_norm_pow').aestronglyMeasurable).symm

theorem wassersteinTwo_le_plan (μ ν : ProbabilityMeasure E) (π : ProbabilityMeasure (E × E))
    (hπ : π ∈ plans μ ν) (hμ : MemLp id 2 (μ : Measure E)) (hν : MemLp id 2 (ν : Measure E)) :
    wassersteinTwo μ ν ≤ Real.sqrt (squaredCost π).toReal := by
  apply Real.sqrt_le_sqrt
  apply ENNReal.toReal_mono
    (squaredCost_finite μ ν π hπ hμ.integrable_norm_pow' hν.integrable_norm_pow')
  exact iInf₂_le π hπ

theorem gluedPlan_cost (μ ν ξ : ProbabilityMeasure E) (π ρ : ProbabilityMeasure (E × E))
    (hπ : π ∈ plans μ ν) (hρ : ρ ∈ plans ν ξ)
    (hμ : MemLp id 2 (μ : Measure E)) (hν : MemLp id 2 (ν : Measure E))
    (hξ : MemLp id 2 (ξ : Measure E)) :
    Real.sqrt (squaredCost (gluedPlan π ρ)).toReal ≤
      Real.sqrt (squaredCost π).toReal+Real.sqrt (squaredCost ρ).toReal := by
  have hmatch : (π : Measure (E × E)).snd=(ρ : Measure (E × E)).fst :=
    (congrArg (fun p : ProbabilityMeasure E => (p : Measure E)) hπ.2).trans
      (congrArg (fun p : ProbabilityMeasure E => (p : Measure E)) hρ.1).symm
  have hπ2 : MemLp (fun z : E × E => z.1-z.2) 2 (π : Measure (E × E)) :=
    (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr
      (squaredCost_integrable μ ν π hπ hμ.integrable_norm_pow' hν.integrable_norm_pow')
  have hρ2 : MemLp (fun z : E × E => z.1-z.2) 2 (ρ : Measure (E × E)) :=
    (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr
      (squaredCost_integrable ν ξ ρ hρ hν.integrable_norm_pow' hξ.integrable_norm_pow')
  have hf : MemLp (fun z : (E × E) × E => z.1.1-z.1.2) 2 (glueMeasure π ρ) := by
    rw [← glueMeasure_left π ρ] at hπ2
    exact (memLp_map_measure_iff (by fun_prop) measurable_fst.aemeasurable).mp hπ2
  have hg : MemLp (fun z : (E × E) × E => z.1.2-z.2) 2 (glueMeasure π ρ) := by
    rw [← glueMeasure_right π ρ hmatch] at hρ2
    exact (memLp_map_measure_iff (by fun_prop) (by fun_prop)).mp hρ2
  have hc := sqrt_integral_norm_add_le hf hg
  simp only [sub_add_sub_cancel] at hc
  rw [squaredCost_toReal μ ξ _ (gluedPlan_mem μ ν ξ π ρ hπ hρ) hμ hξ,
    squaredCost_toReal μ ν π hπ hμ hν, squaredCost_toReal ν ξ ρ hρ hν hξ]
  have hleft : (∫ z, ‖z.1-z.2‖^2 ∂(gluedPlan π ρ : Measure (E × E))) =
      ∫ z : (E × E) × E, ‖z.1.1-z.2‖^2 ∂glueMeasure π ρ := by
    exact integral_map (by fun_prop) (by fun_prop)
  have hfirst : (∫ z, ‖z.1-z.2‖^2 ∂(π : Measure (E × E))) =
      ∫ z : (E × E) × E, ‖z.1.1-z.1.2‖^2 ∂glueMeasure π ρ := by
    rw [← glueMeasure_left π ρ]
    exact integral_map measurable_fst.aemeasurable (by fun_prop)
  have hsecond : (∫ z, ‖z.1-z.2‖^2 ∂(ρ : Measure (E × E))) =
      ∫ z : (E × E) × E, ‖z.1.2-z.2‖^2 ∂glueMeasure π ρ := by
    rw [← glueMeasure_right π ρ hmatch]
    exact integral_map (by fun_prop) (by fun_prop)
  rw [hleft,hfirst,hsecond]
  exact hc

theorem wassersteinTwo_triangle (μ ν ξ : ProbabilityMeasure E)
    (hμ : MemLp id 2 (μ : Measure E)) (hν : MemLp id 2 (ν : Measure E))
    (hξ : MemLp id 2 (ξ : Measure E)) :
    wassersteinTwo μ ξ ≤ wassersteinTwo μ ν+wassersteinTwo ν ξ := by
  have hπ := optimalPlan_optimal μ ν
  have hρ := optimalPlan_optimal ν ξ
  have hb := (wassersteinTwo_le_plan μ ξ _
    (gluedPlan_mem μ ν ξ (optimalPlan μ ν) (optimalPlan ν ξ) hπ.1 hρ.1) hμ hξ).trans
    (gluedPlan_cost μ ν ξ _ _ hπ.1 hρ.1 hμ hν hξ)
  rw [hπ.2,hρ.2] at hb
  exact hb

end QuadraticTransport
end PersistencePays
#print axioms PersistencePays.QuadraticTransport.wassersteinTwo_triangle
