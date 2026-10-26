import PersistencePays.MaximalNoiseCoupling

/-! An actual measurable sticky coupling of adjusted epochs, with the
unadjusted contraction and both rejection probabilities charged explicitly. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {S : Type*} [MeasurableSpace S]

theorem probabilityTV_self (μ : Measure S) : probabilityTV μ μ = 0 := by
  simp [probabilityTV]

theorem probabilityTV_symm (μ ν : Measure S) : probabilityTV μ ν = probabilityTV ν μ := by
  simp only [probabilityTV, abs_sub_comm]

theorem probabilityTV_triangle (μ ν ρ : Measure S) :
    probabilityTV μ ρ ≤ probabilityTV μ ν + probabilityTV ν ρ := by
  apply iSup_le
  intro A
  apply iSup_le
  intro hA
  calc
    ENNReal.ofReal |μ.real A-ρ.real A| ≤
        ENNReal.ofReal (|μ.real A-ν.real A|+|ν.real A-ρ.real A|) :=
      ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)
    _ = ENNReal.ofReal |μ.real A-ν.real A|+ENNReal.ofReal |ν.real A-ρ.real A| :=
      ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ _ := by
      have h1 : ENNReal.ofReal |μ.real A-ν.real A| ≤ probabilityTV μ ν :=
        le_iSup_of_le A (le_iSup_of_le hA le_rfl)
      have h2 : ENNReal.ofReal |ν.real A-ρ.real A| ≤ probabilityTV ν ρ :=
        le_iSup_of_le A (le_iSup_of_le hA le_rfl)
      exact add_le_add h1 h2

end PersistencePays

namespace PersistencePays.OBABOPath
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Actual probability of at least one rejection in one epoch. -/
def epochRejectionProbability (U : E → ℝ) (g : E → E) (h r σ : ℝ) (n : ℕ) (z : E×E) : ℝ≥0∞ :=
  epochRandomness (E:=E) n {p | ¬ everyMoveAccepted U g h r σ
    (fun k => firstNoise n k p.1) (fun k => secondNoise n k p.1) z p.2 n}

/-- The coupling acts on the actual adjusted epoch kernel; all its marginals
therefore include every threshold update and every rejected proposal. -/
def adjustedPairKernel (U : E → ℝ) (hU : Measurable U) (g : E → E) (hg : Measurable g)
    (h r σ : ℝ) (n : ℕ) : Kernel ((E×E)×(E×E)) ((E×E)×(E×E)) :=
  MaximalCoupling.maximalKernel
    ((epochKernel U hU g hg h r σ n).comap Prod.fst measurable_fst)
    ((epochKernel U hU g hg h r σ n).comap Prod.snd measurable_snd)

instance adjustedPairKernel_markov (U : E → ℝ) (hU : Measurable U)
    (g : E → E) (hg : Measurable g) (h r σ : ℝ) (n : ℕ) :
    IsMarkovKernel (adjustedPairKernel U hU g hg h r σ n) := by
  unfold adjustedPairKernel
  infer_instance

theorem adjustedPairKernel_fst (U : E → ℝ) (hU : Measurable U)
    (g : E → E) (hg : Measurable g) (h r σ : ℝ) (n : ℕ) :
    (adjustedPairKernel U hU g hg h r σ n).fst =
      (epochKernel U hU g hg h r σ n).comap Prod.fst measurable_fst :=
  MaximalCoupling.maximalKernel_fst _ _

theorem adjustedPairKernel_snd (U : E → ℝ) (hU : Measurable U)
    (g : E → E) (hg : Measurable g) (h r σ : ℝ) (n : ℕ) :
    (adjustedPairKernel U hU g hg h r σ n).snd =
      (epochKernel U hU g hg h r σ n).comap Prod.snd measurable_snd :=
  MaximalCoupling.maximalKernel_snd _ _

theorem adjustedPairKernel_disagreement (U : E → ℝ) (hU : Measurable U)
    (g : E → E) (hg : Measurable g) (h r σ : ℝ) (n : ℕ) (z z' : E×E) :
    adjustedPairKernel U hU g hg h r σ n (z,z') {p | p.1≠p.2} =
      probabilityTV (epochKernel U hU g hg h r σ n z) (epochKernel U hU g hg h r σ n z') :=
  MaximalCoupling.maximalKernel_disagreement _ _
    ((measurableSet_eq_fun measurable_fst measurable_snd).compl) (z,z')

/-- Once the two adjusted copies meet, they stay together at every epoch boundary. -/
theorem adjustedPairKernel_sticky (U : E → ℝ) (hU : Measurable U)
    (g : E → E) (hg : Measurable g) (h r σ : ℝ) (n : ℕ) (z : E×E) :
    adjustedPairKernel U hU g hg h r σ n (z,z) {p | p.1≠p.2} = 0 := by
  rw [adjustedPairKernel_disagreement, probabilityTV_self]

/-- The exact local coupling estimate used in Proposition 5.3. -/
theorem adjustedPairKernel_local (U : E → ℝ) (hU : Measurable U)
    (g : E → E) (hg : Measurable g) (h r σ : ℝ) (n : ℕ) (z z' : E×E) :
    adjustedPairKernel U hU g hg h r σ n (z,z') {p | p.1≠p.2} ≤
      probabilityTV (unadjustedEpochKernel g hg h r σ n z) (unadjustedEpochKernel g hg h r σ n z') +
        epochRejectionProbability U g h r σ n z + epochRejectionProbability U g h r σ n z' := by
  rw [adjustedPairKernel_disagreement]
  calc
    _ ≤ probabilityTV (epochKernel U hU g hg h r σ n z) (unadjustedEpochKernel g hg h r σ n z) +
        probabilityTV (unadjustedEpochKernel g hg h r σ n z) (epochKernel U hU g hg h r σ n z') :=
      probabilityTV_triangle _ _ _
    _ ≤ epochRejectionProbability U g h r σ n z +
        (probabilityTV (unadjustedEpochKernel g hg h r σ n z) (unadjustedEpochKernel g hg h r σ n z') +
          epochRejectionProbability U g h r σ n z') := by
      apply add_le_add (adjusted_unadjusted_epoch_probabilityTV U hU g hg h r σ n z)
      apply (probabilityTV_triangle _ (unadjustedEpochKernel g hg h r σ n z') _).trans
      apply add_le_add le_rfl
      rw [probabilityTV_symm]
      exact adjusted_unadjusted_epoch_probabilityTV U hU g hg h r σ n z'
    _ = _ := by ac_rfl

end PersistencePays.OBABOPath
#print axioms PersistencePays.OBABOPath.adjustedPairKernel_local
#print axioms PersistencePays.OBABOPath.adjustedPairKernel_sticky
