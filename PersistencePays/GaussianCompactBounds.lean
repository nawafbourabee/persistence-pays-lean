import PersistencePays.GaussianMeanGrowth
import PersistencePays.GaussianMeanFlow

noncomputable section
namespace PersistencePays
open MeasureTheory Set
open scoped NNReal
universe u
variable {E Z:Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace Z] [CompactSpace Z]

theorem compact_regression_uniform_bounds (g:Z→E×E) (hg:Continuous g)
    {ε:ℝ} (hε:ε≠0) :
    ∃ A B:ℝ≥0, (∀s z,‖regressionLatentMean s (g z)‖≤A) ∧
      (∀s z,‖regressionScore ε s (g z)‖≤B) := by
  obtain ⟨R,hR,hr⟩:=(isCompact_range hg).isBounded.exists_pos_norm_le
  refine ⟨⟨2*R,by positivity⟩,⟨2*R/ε^2,by positivity⟩,?_,?_⟩
  · intro s z
    exact regressionLatentMean_norm_bound hR.le s (g z)
      ((norm_fst_le (g z)).trans (hr _ (mem_range_self z)))
      ((norm_snd_le (g z)).trans (hr _ (mem_range_self z)))
  · intro s z
    exact regressionScore_norm_bound hR.le hε s (g z)
      ((norm_fst_le (g z)).trans (hr _ (mem_range_self z)))
      ((norm_snd_le (g z)).trans (hr _ (mem_range_self z)))
end PersistencePays
#print axioms PersistencePays.compact_regression_uniform_bounds
