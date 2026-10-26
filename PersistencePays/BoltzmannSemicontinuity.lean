import PersistencePays.PositionBoltzmannEntropy
import PersistencePays.EntropySemicontinuity

/-! The finite-entropy form of Lemma 4.6 for the genuine Lebesgue-density entropy.
The second-moment convergence is explicit; no continuity of entropy is assumed. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal Topology

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S] [PolishSpace S]

theorem klDiv_toReal_eventually_gt
    (μn : ℕ → ProbabilityMeasure S) (μ γ : ProbabilityMeasure S)
    (hw : Tendsto μn atTop (𝓝 μ))
    (hKn : ∀ n, klDiv (μn n : Measure S) (γ : Measure S) ≠ ∞)
    (hK : klDiv (μ : Measure S) (γ : Measure S) ≠ ∞)
    {b : ℝ} (hb : b < (klDiv (μ : Measure S) (γ : Measure S)).toReal) :
    ∀ᶠ n in atTop, b < (klDiv (μn n : Measure S) (γ : Measure S)).toReal := by
  by_cases hb0 : 0 ≤ b
  · have he := (hw.prodMk_nhds tendsto_const_nhds).eventually
      ((klDiv_joint_lowerSemicontinuous (S:=S) (μ,γ)) (ENNReal.ofReal b)
        ((ENNReal.ofReal_lt_iff_lt_toReal hb0 hK).mpr hb))
    exact he.mono (fun n hn => (ENNReal.ofReal_lt_iff_lt_toReal hb0 (hKn n)).mp hn)
  · exact Filter.Eventually.of_forall (fun n => (lt_of_not_ge hb0).trans_le ENNReal.toReal_nonneg)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Differential entropy is upper semicontinuous along weak convergence with
convergent second moments, stated as the equivalent eventual lower bound for
Boltzmann entropy. All displayed entropies are genuine finite density integrals. -/
theorem boltzmannEntropy_eventually_gt
    (μn : ℕ → ProbabilityMeasure E) (μ : ProbabilityMeasure E)
    (hμn : ∀ n, MemLp id 2 (μn n : Measure E)) (hμ : MemLp id 2 (μ : Measure E))
    (hKn : ∀ n, klDiv (μn n : Measure E) (stdGaussian E) ≠ ∞)
    (hK : klDiv (μ : Measure E) (stdGaussian E) ≠ ∞)
    (hw : Tendsto μn atTop (𝓝 μ))
    (hm : Tendsto (fun n => ∫ x, ‖x‖^2 ∂(μn n : Measure E)) atTop
      (𝓝 (∫ x, ‖x‖^2 ∂(μ : Measure E))))
    {b : ℝ} (hb : b < boltzmannEntropy (μ : Measure E)) :
    ∀ᶠ n in atTop, b < boltzmannEntropy (μn n : Measure E) := by
  let δ := (boltzmannEntropy (μ : Measure E)-b)/4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let γ : ProbabilityMeasure E := ⟨stdGaussian E,inferInstance⟩
  have hkl := klDiv_toReal_eventually_gt μn μ γ hw hKn hK
    (b := (klDiv (μ : Measure E) (stdGaussian E)).toReal-δ) (by dsimp [γ]; linarith)
  have hmoment := hm.eventually (gt_mem_nhds (show (∫ x, ‖x‖^2 ∂(μ : Measure E)) <
    (∫ x, ‖x‖^2 ∂(μ : Measure E))+δ by linarith))
  filter_upwards [hkl,hmoment] with n hn hnM
  rw [(gaussian_boltzmann_identity _ (hμn n) (hKn n)).2]
  have hlim := (gaussian_boltzmann_identity _ hμ hK).2
  dsimp [γ] at hn
  dsimp [δ] at hn hnM
  linarith

end PersistencePays
#print axioms PersistencePays.boltzmannEntropy_eventually_gt
