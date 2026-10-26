import PersistencePays.McCannEntropy
import PersistencePays.GibbsPositionMoment
import PersistencePays.FiniteMoments
import PersistencePays.BrenierInverse
import PersistencePays.Corrector

/-! Actual Gibbs-source quadratic transport: all moment and entropy identities
needed by Talagrand's inequality, and the integrated strong-convexity bound.
The final log-Jacobian/divergence inequality is deliberately not assumed here.
It remains a separate analytic theorem. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def A1.gibbsProbability {U : E → ℝ} {m L : ℝ} (a : A1 U m L) : ProbabilityMeasure E :=
  ⟨positionGibbs U,a.gibbs_isProbabilityMeasure⟩

def A1.gibbsBrenierMap {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (ν : ProbabilityMeasure E) : E → E :=
  QuadraticTransport.brenierMap a.gibbsProbability ν

theorem A1.gibbsBrenierMap_spec {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (ν : ProbabilityMeasure E) (hν : MemLp id 2 (ν : Measure E)) :
    Measurable (a.gibbsBrenierMap ν) ∧
      (positionGibbs U).map (a.gibbsBrenierMap ν) = (ν : Measure E) ∧
      MemLp (a.gibbsBrenierMap ν) 2 (positionGibbs U) := by
  have hs := QuadraticTransport.brenierMap_spec a.gibbsProbability ν
    a.position_memLp_two hν (tilted_absolutelyContinuous volume (-U))
  exact ⟨hs.1,hs.2.1,QuadraticTransport.brenierMap_memLp a.gibbsProbability ν
    a.position_memLp_two hν (tilted_absolutelyContinuous volume (-U))⟩

theorem A1.gibbsBrenier_force_integrable {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (ν : ProbabilityMeasure E) (hν : MemLp id 2 (ν : Measure E)) :
    Integrable (fun x => ⟪gradient U x,a.gibbsBrenierMap ν x-x⟫_ℝ) (positionGibbs U) := by
  letI : IsProbabilityMeasure (positionGibbs U) := a.gibbs_isProbabilityMeasure
  exact integrable_inner_of_memLp_two (a.gradient_memLp a.position_memLp_two)
    ((a.gibbsBrenierMap_spec ν hν).2.2.sub a.position_memLp_two)

theorem A1.gibbsBrenier_potential_integral {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (ν : ProbabilityMeasure E) (hν : MemLp id 2 (ν : Measure E)) :
    (∫ x, U (a.gibbsBrenierMap ν x) ∂positionGibbs U) = ∫ x, U x ∂(ν : Measure E) := by
  have hs := a.gibbsBrenierMap_spec ν hν
  rw [← hs.2.1]
  exact (integral_map hs.1.aemeasurable
    a.twice_contDiff.continuous.measurable.aestronglyMeasurable).symm

theorem A1.gibbsBrenier_strong_convexity {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (ν : ProbabilityMeasure E) (hν : MemLp id 2 (ν : Measure E)) :
    (∫ x, ⟪gradient U x,a.gibbsBrenierMap ν x-x⟫_ℝ ∂positionGibbs U) +
      m/2*(QuadraticTransport.cost a.gibbsProbability ν).toReal ≤
        (∫ x, U x ∂(ν : Measure E))-(∫ x, U x ∂positionGibbs U) := by
  letI : IsProbabilityMeasure (positionGibbs U) := a.gibbs_isProbabilityMeasure
  have ht := (a.gibbsBrenierMap_spec ν hν).2.2
  have hu : Integrable U (positionGibbs U) := a.potential_integrable a.position_memLp_two
  have hut := a.potential_integrable ht
  have hforce := a.gibbsBrenier_force_integrable ν hν
  have hnorm : Integrable (fun x => ‖a.gibbsBrenierMap ν x-x‖^2) (positionGibbs U) := by
    simpa only [Pi.sub_apply,id_eq] using (ht.sub a.position_memLp_two).integrable_norm_pow'
  have hi := integral_mono_ae (hforce.add (hnorm.const_mul (m/2))) (hut.sub hu)
    (Filter.Eventually.of_forall (fun x => by
      have hs := a.strong_lower_bound x (a.gibbsBrenierMap ν x)
      change ⟪gradient U x,a.gibbsBrenierMap ν x-x⟫_ℝ +
        m/2*‖a.gibbsBrenierMap ν x-x‖^2 ≤ U (a.gibbsBrenierMap ν x)-U x
      linarith))
  simp only [Pi.add_apply,Pi.sub_apply,id_eq] at hi
  rw [integral_add hforce (hnorm.const_mul (m/2)),integral_const_mul,
    integral_sub hut hu,a.gibbsBrenier_potential_integral ν hν] at hi
  have hc := QuadraticTransport.brenierMap_displacement_cost a.gibbsProbability ν
    a.position_memLp_two hν (tilted_absolutelyContinuous volume (-U))
  have hc' : (∫ x, ‖a.gibbsBrenierMap ν x-x‖^2 ∂positionGibbs U) =
      (QuadraticTransport.cost a.gibbsProbability ν).toReal := by
    change (∫ x, ‖x-a.gibbsBrenierMap ν x‖^2 ∂positionGibbs U) =
      (QuadraticTransport.cost a.gibbsProbability ν).toReal at hc
    simpa only [norm_sub_rev] using hc
  rwa [hc'] at hi

theorem A1.gibbsBrenier_entropy_lower_bound {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (ν : ProbabilityMeasure E) (hν : MemLp id 2 (ν : Measure E))
    (hK : klDiv (ν : Measure E) (positionGibbs U) ≠ ∞) :
    boltzmannEntropy (ν : Measure E)-boltzmannEntropy (positionGibbs U)+
      (∫ x, ⟪gradient U x,a.gibbsBrenierMap ν x-x⟫_ℝ ∂positionGibbs U)+
      m/2*(QuadraticTransport.cost a.gibbsProbability ν).toReal ≤
        (klDiv (ν : Measure E) (positionGibbs U)).toReal := by
  letI : IsProbabilityMeasure (positionGibbs U) := a.gibbs_isProbabilityMeasure
  have hn := (gibbs_boltzmann_identity U a.gibbs_integrable (ν : Measure E)
    (a.potential_integrable hν) hK).2
  have ht := (gibbs_boltzmann_identity U a.gibbs_integrable (positionGibbs U)
    (a.potential_integrable a.position_memLp_two) (by simp)).2
  simp only [klDiv_self,ENNReal.toReal_zero,zero_sub] at ht
  have hs := a.gibbsBrenier_strong_convexity ν hν
  linarith

/-- The actual Brenier Jacobian domain, its finite log integral, and the exact
relative-entropy formula. All density/moment assumptions are proved from A1
and the stated finite KL and second moment of ν. -/
theorem A1.gibbsBrenier_entropy_jacobian {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (ν : ProbabilityMeasure E) (hν : MemLp id 2 (ν : Measure E))
    (hK : klDiv (ν : Measure E) (positionGibbs U) ≠ ∞) :
    ∃ s : Set E, MeasurableSet s ∧ volume sᶜ=0 ∧
      Set.InjOn (a.gibbsBrenierMap ν) s ∧ DifferentiableOn ℝ (a.gibbsBrenierMap ν) s ∧
      Integrable (fun x => Real.log |(fderivWithin ℝ (a.gibbsBrenierMap ν) s x).det|)
        (positionGibbs U) ∧
      (klDiv (ν : Measure E) (positionGibbs U)).toReal =
        (∫ x, U x ∂(ν : Measure E))-(∫ x, U x ∂positionGibbs U)-
          (∫ x, Real.log |(fderivWithin ℝ (a.gibbsBrenierMap ν) s x).det|
            ∂positionGibbs U) := by
  letI : IsProbabilityMeasure (positionGibbs U) := a.gibbs_isProbabilityMeasure
  have hn := gibbs_boltzmann_identity U a.gibbs_integrable (ν : Measure E)
    (a.potential_integrable hν) hK
  have ht := gibbs_boltzmann_identity U a.gibbs_integrable (positionGibbs U)
    (a.potential_integrable a.position_memLp_two) (by simp)
  obtain ⟨s,hs,hs0,hinj,hd,hi,he⟩ := QuadraticTransport.brenier_entropy_change
    a.gibbsProbability ν a.position_memLp_two hν
      (tilted_absolutelyContinuous volume (-U))
      (absolutelyContinuous_tilted a.gibbs_integrable)
      ((klDiv_ne_top_iff.mp hK).1.trans (tilted_absolutelyContinuous volume (-U)))
      ht.1 hn.1
  refine ⟨s,hs,hs0,hinj,hd,hi,?_⟩
  have hh := ht.2
  have hh' := hn.2
  simp only [klDiv_self,ENNReal.toReal_zero,zero_sub] at hh
  change (∫ x, Real.log |(fderivWithin ℝ (a.gibbsBrenierMap ν) s x).det|
    ∂positionGibbs U) = boltzmannEntropy (positionGibbs U)-boltzmannEntropy (ν : Measure E) at he
  linarith

end PersistencePays
#print axioms PersistencePays.A1.gibbsBrenier_strong_convexity
#print axioms PersistencePays.A1.gibbsBrenier_entropy_lower_bound
#print axioms PersistencePays.A1.gibbsBrenier_entropy_jacobian
