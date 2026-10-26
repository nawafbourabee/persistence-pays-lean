import PersistencePays.WarmL2
import PersistencePays.CouplingTV
import PersistencePays.StageKernels

/-! Proposition 5.3: actual finite-step local coupling, using backward first-exit
probabilities and L2 transfer.  No independence of the two copies is assumed. -/
namespace PersistencePays.LocalizedCoupling
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
attribute [local instance] Classical.propDecidable
variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]

/-- Exact backward recursion for exit from `D` at one of times `0,...,n-1`. -/
def exitProbability (P : Kernel S S) (D : Set S) : ℕ → S → ℝ≥0∞
  | 0, _ => 0
  | n+1, x => if x ∈ D then ∫⁻ y, exitProbability P D n y ∂P x else 1

theorem measurable_exitProbability (P : Kernel S S) (D : Set S) (hD : MeasurableSet D)
    (n : ℕ) : Measurable (exitProbability P D n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact (ih.lintegral_kernel).piecewise hD measurable_const

theorem exitProbability_le_one (P : Kernel S S) [IsMarkovKernel P] (D : Set S)
    (n : ℕ) (x : S) : exitProbability P D n x ≤ 1 := by
  induction n generalizing x with
  | zero => exact zero_le
  | succ n ih =>
    unfold exitProbability
    split_ifs with hx
    · calc
        _ ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂P x := lintegral_mono (ih ·)
        _ = 1 := by simp
    · exact le_rfl

/-- Cauchy--Schwarz applies to any measurable probability-valued function. -/
theorem warmL2_function_bound (ν π : Measure S) [IsProbabilityMeasure ν] [IsProbabilityMeasure π]
    (hac : ν ≪ π) (f : S → ℝ≥0∞) (hf : Measurable f) (hb : ∀ x, f x ≤ 1) :
    (∫⁻ x, f x ∂ν) ≤ warmL2 ν π * (∫⁻ x, f x ∂π) ^ (1/2:ℝ) := by
  rw [warmL2_eq_integral, ← lintegral_rnDeriv_mul hac hf.aemeasurable]
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq π Real.HolderConjugate.two_two
    (Measure.measurable_rnDeriv ν π).aemeasurable hf.aemeasurable
  apply hh.trans
  gcongr with x
  rw [ENNReal.rpow_two]
  calc
    (f x)^2 = f x*f x := pow_two _
    _ ≤ f x*1 := mul_le_mul' le_rfl (hb x)
    _ = f x := mul_one _

theorem stationary_exit_bound (P : Kernel S S) [IsMarkovKernel P]
    (π : Measure S) [IsProbabilityMeasure π] (hπ : P ∘ₘ π = π)
    (D : Set S) (hD : MeasurableSet D) (n : ℕ) :
    (∫⁻ x, exitProbability P D n x ∂π) ≤ (n : ℝ≥0∞)*π Dᶜ := by
  induction n with
  | zero => simp [exitProbability]
  | succ n ih =>
    have hm := measurable_exitProbability P D hD n
    calc
      _ ≤ ∫⁻ x, Dᶜ.indicator (fun _ => (1:ℝ≥0∞)) x+
          ∫⁻ y, exitProbability P D n y ∂P x ∂π := by
        apply lintegral_mono
        intro x
        by_cases hx : x ∈ D <;> simp [exitProbability, hx]
      _ = π Dᶜ + ∫⁻ x, exitProbability P D n x ∂π := by
        rw [lintegral_add_left (measurable_const.indicator hD.compl),
          lintegral_indicator_const hD.compl, one_mul,
          ← Measure.lintegral_bind P.aemeasurable hm.aemeasurable, hπ]
      _ ≤ π Dᶜ + (n:ℝ≥0∞)*π Dᶜ := add_le_add le_rfl ih
      _ = _ := by rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]

/-- The finite iterate may be decomposed at its first transition. -/
theorem iterateKernel_succ_right (P : Kernel S S) [IsMarkovKernel P] (n : ℕ) :
    iterateKernel P (n+1) = iterateKernel P n ∘ₖ P := by
  induction n with
  | zero => simp [iterateKernel]
  | succ n ih =>
    change P ∘ₖ iterateKernel P (n+1) = (P ∘ₖ iterateKernel P n) ∘ₖ P
    rw [ih, Kernel.comp_assoc]

/-- A projection of a coupled transition has the specified marginal transition. -/
theorem map_comp_intertwining (C : Kernel S S) [IsMarkovKernel C]
    (P : Kernel T T) [IsMarkovKernel P] (f : S → T) (hf : Measurable f)
    (hC : ∀ x, (C x).map f=P (f x)) (μ : Measure S) [SFinite μ] :
    (C ∘ₘ μ).map f = P ∘ₘ μ.map f := by
  ext A hA
  rw [Measure.map_apply hf hA, Measure.bind_apply (hf hA) C.aemeasurable,
    Measure.bind_apply hA P.aemeasurable, lintegral_map (P.measurable_coe hA) hf]
  apply lintegral_congr
  intro x
  rw [← hC x, Measure.map_apply hf hA]

theorem map_iterate_comp_intertwining (C : Kernel S S) [IsMarkovKernel C]
    (P : Kernel T T) [IsMarkovKernel P] (f : S → T) (hf : Measurable f)
    (hC : ∀ x, (C x).map f=P (f x))
    (μ : Measure S) [IsProbabilityMeasure μ] (n : ℕ) :
    (iterateKernel C n ∘ₘ μ).map f = iterateKernel P n ∘ₘ μ.map f := by
  induction n with
  | zero => simp [iterateKernel]
  | succ n ih =>
    rw [iterateKernel, ← Measure.comp_assoc, map_comp_intertwining C P f hf hC,
      ih, Measure.comp_assoc, ← iterateKernel]

section Pair
variable [MeasurableEq S]

/-- Actual finite endpoint disagreement is bounded by geometric failure plus
the two first-exit probabilities.  This is a backward Markov argument. -/
theorem endpoint_disagreement_bound (P : Kernel S S) [IsMarkovKernel P]
    (C : Kernel (S×S) (S×S)) [IsMarkovKernel C]
    (hfst : ∀ z, (C z).map Prod.fst=P z.1)
    (hsnd : ∀ z, (C z).map Prod.snd=P z.2)
    (D : Set S) (hD : MeasurableSet D) (q : ℝ≥0∞)
    (hsticky : ∀ x, C (x,x) {w | w.1 ≠ w.2}=0)
    (hlocal : ∀ z : S×S, z.1∈D → z.2∈D → C z {w | w.1 ≠ w.2}≤q)
    (n : ℕ) (z : S×S) :
    iterateKernel C n z {w | w.1 ≠ w.2} ≤
      (if z.1 ≠ z.2 then q^n else 0)+exitProbability P D n z.1+exitProbability P D n z.2 := by
  have hM : MeasurableSet {w : S×S | w.1 ≠ w.2} :=
    (measurableSet_eq_fun measurable_fst measurable_snd).compl
  induction n generalizing z with
  | zero =>
    by_cases hz : z.1=z.2 <;> simp [iterateKernel, Kernel.id_apply, Measure.dirac_apply' _ hM, exitProbability, Set.indicator, hz]
  | succ n ih =>
    by_cases hz1 : z.1 ∈ D
    · by_cases hz2 : z.2 ∈ D
      · have hm := measurable_exitProbability P D hD n
        have hstep : C z {w | w.1 ≠ w.2} ≤ if z.1 ≠ z.2 then q else 0 := by
          split_ifs with hn
          · exact hlocal z hz1 hz2
          · have he : z.1=z.2 := not_not.mp hn
            have hz : z=(z.1,z.1) := by ext <;> simp [he]
            rw [hz, hsticky]
        have hIfst : (∫⁻ w, exitProbability P D n w.1 ∂C z) =
            ∫⁻ x, exitProbability P D n x ∂P z.1 := by
          rw [← hfst z, lintegral_map hm measurable_fst]
        have hIsnd : (∫⁻ w, exitProbability P D n w.2 ∂C z) =
            ∫⁻ x, exitProbability P D n x ∂P z.2 := by
          rw [← hsnd z, lintegral_map hm measurable_snd]
        rw [iterateKernel_succ_right, Kernel.comp_apply' _ _ _ hM]
        calc
          _ ≤ ∫⁻ w, {v : S×S | v.1 ≠ v.2}.indicator (fun _ => q^n) w+
              exitProbability P D n w.1+exitProbability P D n w.2 ∂C z := by
            apply lintegral_mono
            intro w
            simpa only [Set.indicator, Set.mem_ofPred_eq] using ih w
          _ = q^n*C z {w | w.1 ≠ w.2}+
              (∫⁻ x, exitProbability P D n x ∂P z.1)+
              (∫⁻ x, exitProbability P D n x ∂P z.2) := by
            have hm1 : Measurable (fun w : S×S =>
                {v : S×S | v.1 ≠ v.2}.indicator (fun _ => q^n) w+exitProbability P D n w.1) :=
              (measurable_const.indicator hM).add (hm.comp measurable_fst)
            rw [lintegral_add_left hm1,
              lintegral_add_left (measurable_const.indicator hM),
              lintegral_indicator_const hM, hIfst, hIsnd]
          _ ≤ q^n*(if z.1 ≠ z.2 then q else 0)+
              (∫⁻ x, exitProbability P D n x ∂P z.1)+
              (∫⁻ x, exitProbability P D n x ∂P z.2) := by gcongr
          _ = _ := by
            simp only [exitProbability, hz1, hz2, ite_true]
            split_ifs <;> simp [pow_succ]
      · calc
          _ ≤ 1 := prob_le_one
          _ ≤ _ := by simp [exitProbability, hz2]
    · calc
        _ ≤ 1 := prob_le_one
        _ ≤ _ := by
          simp only [exitProbability, hz1, ite_false]
          exact le_add_right (le_add_left le_rfl)

/-- Proposition 5.3's full finite-step estimate for an actual measurable sticky
coupling kernel. Its marginal, local failure, and invariant-law hypotheses
are the interfaces discharged by the adjusted sampler construction. -/
theorem localized_coupling_bound (P : Kernel S S) [IsMarkovKernel P]
    (C : Kernel (S×S) (S×S)) [IsMarkovKernel C]
    (hfst : ∀ z, (C z).map Prod.fst=P z.1)
    (hsnd : ∀ z, (C z).map Prod.snd=P z.2)
    (ν π : Measure S) [IsProbabilityMeasure ν] [IsProbabilityMeasure π]
    (hac : ν ≪ π) (hπ : P ∘ₘ π=π)
    (D : Set S) (hD : MeasurableSet D) (q : ℝ≥0∞)
    (hsticky : ∀ x, C (x,x) {w | w.1 ≠ w.2}=0)
    (hlocal : ∀ z : S×S, z.1∈D → z.2∈D → C z {w | w.1 ≠ w.2}≤q)
    (n : ℕ) :
    probabilityTV (iterateKernel P n ∘ₘ ν) π ≤
      q^n+(n:ℝ≥0∞)*π Dᶜ+warmL2 ν π*((n:ℝ≥0∞)*π Dᶜ)^(1/2:ℝ) := by
  let ρ := iterateKernel C n ∘ₘ ν.prod π
  have hM : MeasurableSet {w : S×S | w.1 ≠ w.2} :=
    (measurableSet_eq_fun measurable_fst measurable_snd).compl
  have hf : ρ.map Prod.fst = iterateKernel P n ∘ₘ ν := by
    dsimp only [ρ]
    rw [map_iterate_comp_intertwining C P Prod.fst measurable_fst hfst,
      Measure.map_fst_prod, measure_univ, one_smul]
  have hs : ρ.map Prod.snd = π := by
    dsimp only [ρ]
    rw [map_iterate_comp_intertwining C P Prod.snd measurable_snd hsnd,
      Measure.map_snd_prod, measure_univ, one_smul, iterateKernel_invariant P π hπ]
  have hm := measurable_exitProbability P D hD n
  have hIfst : (∫⁻ w : S×S, exitProbability P D n w.1 ∂ν.prod π) =
      ∫⁻ x, exitProbability P D n x ∂ν := by
    rw [← lintegral_map hm measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]
  have hIsnd : (∫⁻ w : S×S, exitProbability P D n w.2 ∂ν.prod π) =
      ∫⁻ x, exitProbability P D n x ∂π := by
    rw [← lintegral_map hm measurable_snd, Measure.map_snd_prod, measure_univ, one_smul]
  calc
    probabilityTV (iterateKernel P n ∘ₘ ν) π ≤ ρ {w | w.1 ≠ w.2} := by
      simpa only [hf, hs] using coupling_probabilityTV ρ Prod.fst Prod.snd measurable_fst measurable_snd
    _ = ∫⁻ z, iterateKernel C n z {w | w.1 ≠ w.2} ∂ν.prod π :=
      Measure.bind_apply hM (Kernel.aemeasurable _)
    _ ≤ ∫⁻ z : S×S, q^n+exitProbability P D n z.1+exitProbability P D n z.2 ∂ν.prod π := by
      apply lintegral_mono
      intro z
      apply (endpoint_disagreement_bound P C hfst hsnd D hD q hsticky hlocal n z).trans
      exact add_le_add (add_le_add (by split_ifs <;> simp) le_rfl) le_rfl
    _ = q^n+(∫⁻ x, exitProbability P D n x ∂ν)+
        (∫⁻ x, exitProbability P D n x ∂π) := by
      have hm1 : Measurable (fun z : S×S => q^n+exitProbability P D n z.1) :=
        measurable_const.add (hm.comp measurable_fst)
      rw [lintegral_add_left hm1, lintegral_add_left measurable_const,
        lintegral_const, measure_univ, mul_one, hIfst, hIsnd]
    _ ≤ q^n+warmL2 ν π*((n:ℝ≥0∞)*π Dᶜ)^(1/2:ℝ)+(n:ℝ≥0∞)*π Dᶜ := by
      have hw := warmL2_function_bound ν π hac (exitProbability P D n) hm
        (exitProbability_le_one P D n)
      have he := stationary_exit_bound P π hπ D hD n
      gcongr
      exact hw.trans (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow he (by positivity)))
    _ = _ := by ac_rfl

end Pair

end
end PersistencePays.LocalizedCoupling

#print axioms PersistencePays.LocalizedCoupling.localized_coupling_bound
