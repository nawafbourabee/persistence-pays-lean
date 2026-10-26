import PersistencePays.Brenier
import Mathlib.MeasureTheory.Function.L2Space

/-! A fixed law-dependent version of the quadratic optimal transport map.
Its defining properties are proved from the Brenier theorem, not postulated. -/
noncomputable section
namespace PersistencePays.QuadraticTransport
open MeasureTheory Set
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def optimalPlan (μ ν : ProbabilityMeasure E) : ProbabilityMeasure (E × E) :=
  Classical.choose (exists_optimal μ ν)

theorem optimalPlan_optimal (μ ν : ProbabilityMeasure E) : IsOptimal μ ν (optimalPlan μ ν) :=
  Classical.choose_spec (exists_optimal μ ν)

def RepresentsOptimalMap (μ ν : ProbabilityMeasure E) (T : E → E) : Prop :=
  Measurable T ∧ (μ : Measure E).map T = (ν : Measure E) ∧
    (optimalPlan μ ν : Measure (E × E)) = (μ : Measure E).map (fun x => (x,T x))

def brenierMap (μ ν : ProbabilityMeasure E) : E → E := by
  classical
  exact if h : ∃ T, RepresentsOptimalMap μ ν T then Classical.choose h else fun _ => 0

theorem exists_representsOptimalMap (μ ν : ProbabilityMeasure E)
    (hμ : MemLp id 2 (μ : Measure E)) (hν : MemLp id 2 (ν : Measure E))
    (hac : (μ : Measure E) ≪ volume) : ∃ T, RepresentsOptimalMap μ ν T := by
  obtain ⟨a,_,_,hm,hmap,hgraph⟩ := brenier_gradient μ ν (optimalPlan μ ν)
    (optimalPlan_optimal μ ν)
    (squaredCost_finite μ ν (optimalPlan μ ν) (optimalPlan_optimal μ ν).1
      hμ.integrable_norm_pow' hν.integrable_norm_pow') volume hac
  exact ⟨_,hm,hmap,hgraph⟩

theorem brenierMap_spec (μ ν : ProbabilityMeasure E)
    (hμ : MemLp id 2 (μ : Measure E)) (hν : MemLp id 2 (ν : Measure E))
    (hac : (μ : Measure E) ≪ volume) : RepresentsOptimalMap μ ν (brenierMap μ ν) := by
  have he := exists_representsOptimalMap μ ν hμ hν hac
  unfold brenierMap
  rw [dite_eq_left he]
  exact Classical.choose_spec he

theorem measurable_brenierMap (μ ν : ProbabilityMeasure E) : Measurable (brenierMap μ ν) := by
  unfold brenierMap
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · exact measurable_const

theorem brenierMap_memLp (μ ν : ProbabilityMeasure E)
    (hμ : MemLp id 2 (μ : Measure E)) (hν : MemLp id 2 (ν : Measure E))
    (hac : (μ : Measure E) ≪ volume) : MemLp (brenierMap μ ν) 2 (μ : Measure E) := by
  have hs := brenierMap_spec μ ν hμ hν hac
  rw [← hs.2.1] at hν
  exact (memLp_map_measure_iff measurable_id.aestronglyMeasurable hs.1.aemeasurable).mp hν

theorem brenierMap_displacement_cost (μ ν : ProbabilityMeasure E)
    (hμ : MemLp id 2 (μ : Measure E)) (hν : MemLp id 2 (ν : Measure E))
    (hac : (μ : Measure E) ≪ volume) :
    (∫ x, ‖x-brenierMap μ ν x‖^2 ∂(μ : Measure E)) = (cost μ ν).toReal := by
  have hs := brenierMap_spec μ ν hμ hν hac
  have hi := (hμ.sub (brenierMap_memLp μ ν hμ hν hac)).integrable_norm_pow'
  have hm : Measurable (fun x => ENNReal.ofReal (‖x-brenierMap μ ν x‖^2)) := by
    exact (measurable_id.sub hs.1).norm.pow_const 2 |>.ennreal_ofReal
  rw [← (optimalPlan_optimal μ ν).2, squaredCost, hs.2.2,
    lintegral_map (by fun_prop) (show Measurable (fun x : E => (x,brenierMap μ ν x)) from
      measurable_id.prodMk hs.1)]
  exact (integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun x => sq_nonneg _))
    hi.aestronglyMeasurable)

end PersistencePays.QuadraticTransport
#print axioms PersistencePays.QuadraticTransport.brenierMap_spec
#print axioms PersistencePays.QuadraticTransport.brenierMap_displacement_cost
