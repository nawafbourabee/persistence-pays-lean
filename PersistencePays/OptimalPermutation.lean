import PersistencePays.PermutationCompetitor
import PersistencePays.ProductSupport
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! A finite permutation cannot reduce the cost on the support of an optimal plan. -/
noncomputable section
namespace PersistencePays.QuadraticTransport
open MeasureTheory Set Filter
open scoped ENNReal
variable {ι E : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [PolishSpace E]

def pointSquaredCost (z : E×E) : ℝ≥0∞ := ENNReal.ofReal (‖z.1-z.2‖^2)
def arraySquaredCost (p : ι → E×E) : ℝ≥0∞ := ∑ i, pointSquaredCost (p i)
def permutedSquaredCost (e : Equiv.Perm ι) (p : ι → E×E) : ℝ≥0∞ :=
  ∑ i, pointSquaredCost ((p i).1,(p (e i)).2)

theorem continuous_pointSquaredCost : Continuous (pointSquaredCost (E:=E)) := by
  unfold pointSquaredCost
  exact ENNReal.continuous_ofReal.comp (by fun_prop)

theorem continuous_arraySquaredCost : Continuous (arraySquaredCost (ι:=ι) (E:=E)) := by
  unfold arraySquaredCost
  exact continuous_finset_sum _ fun i _ => continuous_pointSquaredCost.comp (continuous_apply i)

theorem continuous_permutedSquaredCost (e : Equiv.Perm ι) : Continuous (permutedSquaredCost (E:=E) e) := by
  unfold permutedSquaredCost
  exact continuous_finset_sum _ fun i _ => continuous_pointSquaredCost.comp
    ((continuous_apply i).fst.prodMk (continuous_apply (e i)).snd)

theorem optimal_array_permutation_ae (μ ν : ProbabilityMeasure E) (π : ProbabilityMeasure (E×E))
    (hπ : IsOptimal μ ν π) (hfinite : squaredCost π ≠ ∞) (e : Equiv.Perm ι) :
    ∀ᵐ p ∂Measure.pi (fun _ : ι => (π : Measure (E×E))), arraySquaredCost p ≤ permutedSquaredCost e p := by
  classical
  let P := Measure.pi (fun _ : ι => (π : Measure (E×E)))
  let A : Set (ι → E×E) := {p | permutedSquaredCost e p < arraySquaredCost p}
  have hA : MeasurableSet A := measurableSet_lt
    (continuous_permutedSquaredCost e).measurable continuous_arraySquaredCost.measurable
  let ρ : ProbabilityMeasure (E×E) := ⟨rewiredMeasure (π : Measure (E×E)) A e,
    rewiredMeasure_probability _ A hA e⟩
  have hρ : ρ ∈ plans μ ν := by
    constructor
    · apply Subtype.ext
      change (rewiredMeasure (π : Measure (E×E)) A e).map Prod.fst = (μ : Measure E)
      rw [rewiredMeasure_fst _ A hA e]
      exact congrArg (fun p : ProbabilityMeasure E => (p : Measure E)) hπ.1.1
    · apply Subtype.ext
      change (rewiredMeasure (π : Measure (E×E)) A e).map Prod.snd = (ν : Measure E)
      rw [rewiredMeasure_snd _ A hA e]
      exact congrArg (fun p : ProbabilityMeasure E => (p : Measure E)) hπ.1.2
  let c : ℝ≥0∞ := (Fintype.card ι : ℝ≥0∞)
  have hc0 : c ≠ 0 := by dsimp [c]; exact_mod_cast Fintype.card_ne_zero
  have hctop : c ≠ ∞ := by dsimp [c]; simp
  let newCost : (ι → E×E) → ℝ≥0∞ := fun p => ∑ i, pointSquaredCost (rewiredPair A e i p)
  have hnew (p : ι → E×E) : newCost p ≤ arraySquaredCost p := by
    by_cases hp : p ∈ A
    · have hlt : permutedSquaredCost e p < arraySquaredCost p := hp
      simpa only [newCost, rewiredPair, hp, ite_true, permutedSquaredCost] using hlt.le
    · simp only [newCost, rewiredPair, hp, ite_false, arraySquaredCost, le_refl]
  have hold : c⁻¹*(∫⁻ p, arraySquaredCost p ∂P) = squaredCost π := by
    have he := averageMap_eq_of_measure_preserving P (π : Measure (E×E))
      (fun i : ι => Function.eval i) (fun i => measurePreserving_eval _ i)
    have hi := averageMap_lintegral P (fun i : ι => Function.eval i)
      (fun i => measurable_pi_apply i) pointSquaredCost continuous_pointSquaredCost.measurable
    rw [he] at hi
    exact hi.symm
  have hnewcost : squaredCost ρ = c⁻¹*(∫⁻ p, newCost p ∂P) :=
    averageMap_lintegral P (rewiredPair A e) (measurable_rewiredPair A hA e)
      pointSquaredCost continuous_pointSquaredCost.measurable
  have hoptimal : squaredCost π ≤ squaredCost ρ := by
    rw [hπ.2]
    exact iInf₂_le ρ hρ
  have hrev : (∫⁻ p, arraySquaredCost p ∂P) ≤ ∫⁻ p, newCost p ∂P := by
    rw [← hold, hnewcost] at hoptimal
    have hm := mul_le_mul_right hoptimal c
    simpa only [← mul_assoc, ENNReal.mul_inv_cancel hc0 hctop, one_mul] using hm
  have holdfinite : (∫⁻ p, arraySquaredCost p ∂P) ≠ ∞ := by
    have hh : (∫⁻ p, arraySquaredCost p ∂P) = c*squaredCost π := by
      rw [← hold, ← mul_assoc, ENNReal.mul_inv_cancel hc0 hctop, one_mul]
    rw [hh]
    exact ENNReal.mul_ne_top hctop hfinite
  have heq := ae_eq_of_ae_le_of_lintegral_le (μ:=P) (Eventually.of_forall hnew)
    (ne_of_lt ((lintegral_mono hnew).trans_lt (lt_top_iff_ne_top.mpr holdfinite)))
    continuous_arraySquaredCost.measurable.aemeasurable hrev
  filter_upwards [heq] with p hp
  by_contra hb
  have ha : p ∈ A := lt_of_not_ge hb
  have he : newCost p = permutedSquaredCost e p := by simp only [newCost, rewiredPair, ha, ite_true, permutedSquaredCost]
  rw [he] at hp
  exact (ne_of_lt ha) hp

theorem optimal_support_permutation (μ ν : ProbabilityMeasure E) (π : ProbabilityMeasure (E×E))
    (hπ : IsOptimal μ ν π) (hfinite : squaredCost π ≠ ∞) (e : Equiv.Perm ι)
    (p : ι → E×E) (hp : ∀ i, p i ∈ (π : Measure (E×E)).support) :
    arraySquaredCost p ≤ permutedSquaredCost e p := by
  have hclosed : IsClosed {p : ι → E×E | arraySquaredCost p ≤ permutedSquaredCost e p} :=
    isClosed_le continuous_arraySquaredCost (continuous_permutedSquaredCost e)
  exact (Measure.support_subset_of_isClosed hclosed (optimal_array_permutation_ae μ ν π hπ hfinite e))
    (PersistencePays.mem_support_pi (fun _ : ι => (π : Measure (E×E))) p hp)


theorem optimal_support_permutation_real (μ ν : ProbabilityMeasure E) (π : ProbabilityMeasure (E×E))
    (hπ : IsOptimal μ ν π) (hfinite : squaredCost π ≠ ∞) (e : Equiv.Perm ι)
    (p : ι → E×E) (hp : ∀ i, p i ∈ (π : Measure (E×E)).support) :
    (∑ i, ‖(p i).1-(p i).2‖^2) ≤ ∑ i, ‖(p i).1-(p (e i)).2‖^2 := by
  have hh := optimal_support_permutation μ ν π hπ hfinite e p hp
  unfold arraySquaredCost permutedSquaredCost pointSquaredCost at hh
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg ‖(p i).1-(p i).2‖),
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg ‖(p i).1-(p (e i)).2‖)] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg (fun i _ => sq_nonneg ‖(p i).1-(p (e i)).2‖))).mp hh

end PersistencePays.QuadraticTransport
#print axioms PersistencePays.QuadraticTransport.optimal_support_permutation

#print axioms PersistencePays.QuadraticTransport.optimal_support_permutation_real
