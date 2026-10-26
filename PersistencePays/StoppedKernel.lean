import PersistencePays.FiniteNoise
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Subprobability kernels, stopped exponential moments, and their iteration.
The kernels below retain exactly the trajectories that have not yet exited. -/

noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {S B : Type*} [MeasurableSpace S] [MeasurableSpace B]

/-- The substochastic kernel obtained by retaining only good state/noise pairs. -/
def stoppedNoiseKernel (μ : Measure B) (f : S × B → S)
    (G : Set (S × B)) (hG : MeasurableSet G) : Kernel S S :=
  ((Kernel.id ×ₖ Kernel.const S μ).restrict hG).map f

instance stoppedNoiseKernel_finite (μ : Measure B) [IsProbabilityMeasure μ]
    (f : S × B → S) (G : Set (S × B)) (hG : MeasurableSet G) :
    IsFiniteKernel (stoppedNoiseKernel μ f G hG) := by
  unfold stoppedNoiseKernel
  infer_instance

theorem stoppedNoiseKernel_apply (μ : Measure B) [IsProbabilityMeasure μ]
    (f : S × B → S) (hf : Measurable f)
    (G : Set (S × B)) (hG : MeasurableSet G) (s : S) :
    stoppedNoiseKernel μ f G hG s =
      (μ.restrict {b | (s, b) ∈ G}).map (fun b => f (s, b)) := by
  have hfs : Measurable (fun b : B => f (s,b)) :=
    hf.comp (measurable_const.prodMk measurable_id)
  ext A hA
  rw [stoppedNoiseKernel, Kernel.map_apply' _ hf _ hA,
    Kernel.restrict_apply' _ hG _ (hf hA),
    Kernel.id_prod_apply' _ _ ((hf hA).inter hG), Kernel.const_apply,
    Measure.map_apply hfs hA, Measure.restrict_apply (hfs hA)]
  rfl

theorem stoppedNoiseKernel_mass_le_one (μ : Measure B) [IsProbabilityMeasure μ]
    (f : S × B → S) (hf : Measurable f)
    (G : Set (S × B)) (hG : MeasurableSet G) (s : S) :
    stoppedNoiseKernel μ f G hG s univ ≤ 1 := by
  have hfs : Measurable (fun b : B => f (s,b)) :=
    hf.comp (measurable_const.prodMk measurable_id)
  rw [stoppedNoiseKernel_apply μ f hf G hG,
    Measure.map_apply hfs MeasurableSet.univ]
  simp only [preimage_univ, Measure.restrict_apply MeasurableSet.univ, univ_inter]
  exact prob_le_one

theorem stoppedNoiseKernel_lintegral (μ : Measure B) [IsProbabilityMeasure μ]
    (f : S × B → S) (hf : Measurable f)
    (G : Set (S × B)) (hG : MeasurableSet G) (s : S)
    (F : S → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ z, F z ∂stoppedNoiseKernel μ f G hG s =
      ∫⁻ b in {b | (s,b) ∈ G}, F (f (s,b)) ∂μ := by
  have hfs : Measurable (fun b : B => f (s,b)) :=
    hf.comp (measurable_const.prodMk measurable_id)
  rw [stoppedNoiseKernel_apply μ f hf G hG,
    lintegral_map hF hfs]

/-- Iterating a kernel of mass at most one never creates probability mass. -/
theorem iterateKernel_mass_le_one (K : Kernel S S)
    (hmass : ∀ z, K z univ ≤ 1) (n : ℕ) (z : S) :
    iterateKernel K n z univ ≤ 1 := by
  induction n with
  | zero => simp [iterateKernel, Kernel.id_apply]
  | succ n ih =>
    rw [iterateKernel, Kernel.comp_apply' _ _ _ MeasurableSet.univ]
    calc
      _ ≤ ∫⁻ _w, (1 : ℝ≥0∞) ∂iterateKernel K n z := lintegral_mono hmass
      _ = iterateKernel K n z univ := by simp
      _ ≤ 1 := ih

/-- Convexity of the exponential gives the linear drift needed for stopped
iteration, without taking the logarithm of a possibly zero expectation. -/
theorem exponential_affine_drift {a b q v : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : b ≤ a*q) :
    Real.exp ((1-a)*v+b) ≤ (1-a)*Real.exp v+a*Real.exp q := by
  calc
    _ ≤ Real.exp ((1-a)*v+a*q) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ _ := convexOn_exp.2 (mem_univ v) (mem_univ q)
      (by linarith) ha (by ring)

/-- A linear Lyapunov drift and an initial bound propagate through every
iterate of the actual subprobability kernel. -/
theorem iterateKernel_moment_bound (K : Kernel S S)
    (hmass : ∀ z, K z univ ≤ 1) (F : S → ℝ≥0∞) (hF : Measurable F)
    (c C : ℝ≥0∞) (hc : c ≤ 1)
    (hdrift : ∀ z, ∫⁻ w, F w ∂K z ≤ c*F z+(1-c)*C)
    (z : S) (hz : F z ≤ C) (n : ℕ) :
    ∫⁻ w, F w ∂iterateKernel K n z ≤ C := by
  induction n with
  | zero => simpa only [iterateKernel, Kernel.id_apply, lintegral_dirac' _ hF] using hz
  | succ n ih =>
    rw [iterateKernel, Kernel.lintegral_comp _ _ _ hF]
    calc
      _ ≤ ∫⁻ w, (c*F w+(1-c)*C) ∂iterateKernel K n z :=
        lintegral_mono hdrift
      _ = c*(∫⁻ w, F w ∂iterateKernel K n z)+
          ((1-c)*C)*iterateKernel K n z univ := by
        rw [lintegral_add_left (hF.const_mul c), lintegral_const_mul c hF,
          lintegral_const]
      _ ≤ c*C+((1-c)*C)*1 := by
        exact add_le_add (mul_le_mul_right ih c)
          (mul_le_mul_right (iterateKernel_mass_le_one K hmass n z) _)
      _ = C := by
        rw [mul_one, ← add_mul, add_tsub_cancel_of_le hc, one_mul]

theorem iterateKernel_exponential_bound (K : Kernel S S)
    (hmass : ∀ z, K z univ ≤ 1) (V : S → ℝ) (hV : Measurable V)
    {a b q : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : b ≤ a*q)
    (hdrift : ∀ z, ∫⁻ w, ENNReal.ofReal (Real.exp (V w)) ∂K z ≤
      ENNReal.ofReal (Real.exp ((1-a)*V z+b)))
    (z : S) (hz : V z ≤ q) (n : ℕ) :
    ∫⁻ w, ENNReal.ofReal (Real.exp (V w)) ∂iterateKernel K n z ≤
      ENNReal.ofReal (Real.exp q) := by
  apply iterateKernel_moment_bound K hmass _ hV.exp.ennreal_ofReal
    (ENNReal.ofReal (1-a)) (ENNReal.ofReal (Real.exp q))
    (by simpa using ENNReal.ofReal_le_ofReal (show 1-a ≤ 1 by linarith)) _ z
    (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hz)) n
  intro w
  apply (hdrift w).trans
  have hh := ENNReal.ofReal_le_ofReal
    (exponential_affine_drift (v := V w) ha ha1 hb)
  have h1a : 0 ≤ 1-a := sub_nonneg.mpr ha1
  have hsub : 1-ENNReal.ofReal (1-a) = ENNReal.ofReal a := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 h1a]
    congr 1
    ring
  rw [hsub]
  rw [ENNReal.ofReal_add (mul_nonneg h1a (Real.exp_nonneg _))
    (mul_nonneg ha (Real.exp_nonneg _)),
    ENNReal.ofReal_mul h1a, ENNReal.ofReal_mul ha] at hh
  exact hh

/-- Exponential Markov inequality in a form that requires only the displayed
Lebesgue integral bound, and no separate integrability premise. -/
theorem exponential_tail_of_lintegral_bound (μ : Measure S) (V : S → ℝ)
    (hV : Measurable V) {θ q s : ℝ} (hθ : 0 ≤ θ)
    (hm : (∫⁻ x, ENNReal.ofReal (Real.exp (θ*V x)) ∂μ) ≤
      ENNReal.ofReal (Real.exp (θ*q))) :
    μ {x | s < V x} ≤ ENNReal.ofReal (Real.exp (-θ*(s-q))) := by
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (-θ*s))*
        ENNReal.ofReal (Real.exp (θ*V x)) ∂μ := by
      apply meas_le_lintegral₀
        ((hV.const_mul θ).exp.ennreal_ofReal.const_mul _).aemeasurable
      intro x hx
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      apply (show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by norm_num).le.trans
      exact ENNReal.ofReal_le_ofReal (Real.one_le_exp_iff.mpr
        (by nlinarith [mul_le_mul_of_nonneg_left (le_of_lt hx) hθ]))
    _ = ENNReal.ofReal (Real.exp (-θ*s))*
        ∫⁻ x, ENNReal.ofReal (Real.exp (θ*V x)) ∂μ :=
      lintegral_const_mul _ (hV.const_mul θ).exp.ennreal_ofReal
    _ ≤ ENNReal.ofReal (Real.exp (-θ*s))*ENNReal.ofReal (Real.exp (θ*q)) :=
      mul_le_mul_right hm _
    _ = _ := by
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      congr 2
      ring

/-- The total probability lost by a killed kernel is at most the sum of its
one-step losses along the surviving laws. -/
theorem iterateKernel_loss_bound (K : Kernel S S)
    (hmass : ∀ z, K z univ ≤ 1) (δ : ℝ≥0∞) (z : S)
    (hloss : ∀ n, (∫⁻ w, 1-K w univ ∂iterateKernel K n z) ≤ δ)
    (n : ℕ) : 1-iterateKernel K n z univ ≤ (n : ℝ≥0∞)*δ := by
  suffices 1 ≤ iterateKernel K n z univ+(n : ℝ≥0∞)*δ by
    exact tsub_le_iff_right.mpr (by simpa only [add_comm] using this)
  induction n with
  | zero => simp [iterateKernel, Kernel.id_apply]
  | succ n ih =>
    have hm : Measurable (fun w => K w univ) := K.measurable_coe MeasurableSet.univ
    have hstep : iterateKernel K n z univ ≤ iterateKernel K (n+1) z univ+δ := by
      calc
        _ = ∫⁻ w, (K w univ+(1-K w univ)) ∂iterateKernel K n z := by
          simp only [add_tsub_cancel_of_le (hmass _), lintegral_const, one_mul]
        _ = iterateKernel K (n+1) z univ+
            ∫⁻ w, (1-K w univ) ∂iterateKernel K n z := by
          rw [lintegral_add_left hm, iterateKernel,
            Kernel.comp_apply' _ _ _ MeasurableSet.univ]
        _ ≤ _ := add_le_add le_rfl (hloss n)
    calc
      1 ≤ iterateKernel K n z univ+(n : ℝ≥0∞)*δ := ih
      _ ≤ (iterateKernel K (n+1) z univ+δ)+(n : ℝ≥0∞)*δ :=
        add_le_add hstep le_rfl
      _ = _ := by
        rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
        ac_rfl

end PersistencePays

#print axioms PersistencePays.stoppedNoiseKernel_apply
#print axioms PersistencePays.iterateKernel_moment_bound
#print axioms PersistencePays.iterateKernel_exponential_bound
#print axioms PersistencePays.exponential_tail_of_lintegral_bound
#print axioms PersistencePays.iterateKernel_loss_bound
