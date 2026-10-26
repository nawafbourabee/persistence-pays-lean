import PersistencePays.TransportEntropyBalance
import PersistencePays.TransportEntropySemicontinuity

/-! The actual entropy trapezoid defect: time integrability and Lemma 4.9(i). -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def entropyTrapezoidDefect (μ : Measure (E × E)) (h : ℝ) : ℝ :=
  h/2*(boltzmannEntropy (transportPosition μ 0) + boltzmannEntropy (transportPosition μ h)) -
    ∫ s in (0 : ℝ)..h, boltzmannEntropy (transportPosition μ s)

theorem conditionalGaussianEntropy_intervalIntegrable
    (μ : Measure (E × E)) [IsProbabilityMeasure μ] {h : ℝ} (hh : 0 < h)
    (h0 : conditionalGaussianEntropy μ (stdGaussian E) 0 ≠ ∞)
    (h1 : conditionalGaussianEntropy μ (stdGaussian E) h ≠ ∞) :
    IntervalIntegrable (fun s => (conditionalGaussianEntropy μ (stdGaussian E) s).toReal)
      volume 0 h := by
  let C := (conditionalGaussianEntropy μ (stdGaussian E) 0).toReal +
    (conditionalGaussianEntropy μ (stdGaussian E) h).toReal
  apply (intervalIntegrable_const (c := C)).mono_fun'
    (measurable_conditionalGaussianEntropy μ (stdGaussian E)).ennreal_toReal.aestronglyMeasurable
  apply (ae_restrict_mem measurableSet_uIoc).mono
  intro s hs
  rw [uIoc_of_le hh.le] at hs
  change ‖(conditionalGaussianEntropy μ (stdGaussian E) s).toReal‖ ≤ C
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  have hb := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨h0,h1⟩)
    (corollary_3_5 μ hh hs.1.le hs.2)
  rwa [ENNReal.toReal_add h0 h1] at hb

/-- Lemma 4.9(i), including the time-integrability needed to give both sides
of the trapezoidal identity their ordinary Lebesgue-integral meaning. -/
theorem A1.lemma_4_9_i {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E × E)) [IsProbabilityMeasure μ] {h : ℝ} (hh : 0 < h)
    (hμ : MemLp id 2 μ) (hK : klDiv μ (phaseGibbs U) ≠ ∞) :
    IntervalIntegrable (fun s => boltzmannEntropy (transportPosition μ s)) volume 0 h ∧
    IntervalIntegrable (fun s => (conditionalGaussianEntropy μ (stdGaussian E) s).toReal)
      volume 0 h ∧
    entropyTrapezoidDefect μ h =
      (∫ s in (0 : ℝ)..h, (conditionalGaussianEntropy μ (stdGaussian E) s).toReal) -
        h/2*((conditionalGaussianEntropy μ (stdGaussian E) 0).toReal +
          (conditionalGaussianEntropy μ (stdGaussian E) h).toReal) ∧
    entropyTrapezoidDefect μ h ≤
      h/2*((conditionalGaussianEntropy μ (stdGaussian E) 0).toReal +
        (conditionalGaussianEntropy μ (stdGaussian E) h).toReal) := by
  let C := boltzmannEntropy μ.fst +
    (conditionalGaussianEntropy μ (stdGaussian E) 0).toReal
  have he (s : ℝ) : boltzmannEntropy (transportPosition μ s) =
      C-(conditionalGaussianEntropy μ (stdGaussian E) s).toReal := by
    have hb := (a.free_transport_entropy_balance μ hμ hK s).2.2
    dsimp only [C]
    linarith
  have h0 := (a.free_transport_entropy_balance μ hμ hK 0).1
  have h1 := (a.free_transport_entropy_balance μ hμ hK h).1
  have hi := conditionalGaussianEntropy_intervalIntegrable μ hh h0 h1
  have hl : IntervalIntegrable (fun s => boltzmannEntropy (transportPosition μ s)) volume 0 h := by
    simp_rw [he]
    exact intervalIntegrable_const.sub hi
  have hLi : (∫ s in (0 : ℝ)..h, boltzmannEntropy (transportPosition μ s)) =
      h*C-(∫ s in (0 : ℝ)..h, (conditionalGaussianEntropy μ (stdGaussian E) s).toReal) := by
    simp_rw [he]
    rw [intervalIntegral.integral_sub intervalIntegrable_const hi,
      intervalIntegral.integral_const]
    simp
  have hid : entropyTrapezoidDefect μ h =
      (∫ s in (0 : ℝ)..h, (conditionalGaussianEntropy μ (stdGaussian E) s).toReal) -
        h/2*((conditionalGaussianEntropy μ (stdGaussian E) 0).toReal +
          (conditionalGaussianEntropy μ (stdGaussian E) h).toReal) := by
    unfold entropyTrapezoidDefect
    rw [hLi, he 0, he h]
    ring
  refine ⟨hl,hi,hid,?_⟩
  have hb := intervalIntegral.integral_mono_on hh.le hi
    (intervalIntegrable_const (c := (conditionalGaussianEntropy μ (stdGaussian E) 0).toReal +
      (conditionalGaussianEntropy μ (stdGaussian E) h).toReal)) (fun s hs => by
      have ht := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨h0,h1⟩)
        (corollary_3_5 μ hh hs.1 hs.2)
      rwa [ENNReal.toReal_add h0 h1] at ht)
  rw [intervalIntegral.integral_const] at hb
  simp only [sub_zero, smul_eq_mul] at hb
  rw [hid]
  nlinarith

end PersistencePays
#print axioms PersistencePays.A1.lemma_4_9_i
