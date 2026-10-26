import PersistencePays.GaussianConditionalConvergence
import PersistencePays.FreeTransportCorrectorContinuity
import PersistencePays.FreeTransportLimit

/-! Entropy continuity along every finite-entropy free flight. The full Gaussian
relative entropy is a quadratic polynomial; lower semicontinuity of both terms
in its chain rule gives continuity of each term. No smooth density bounds needed. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem gaussian_freeTransport_entropy_polynomial (μ:Measure (E×E)) [IsProbabilityMeasure μ]
    (hμ:MemLp id 2 μ)
    (hK:klDiv μ (gaussianPairProbability (E:=E):Measure (E×E))≠∞) (t:ℝ) :
    (klDiv (transportJoint μ t) (gaussianPairProbability (E:=E):Measure (E×E))).toReal=
      (klDiv μ (gaussianPairProbability (E:=E):Measure (E×E))).toReal+
      t*(∫z,⟪z.1,z.2⟫ ∂μ)+(t^2/2)*(∫z,‖z.2‖^2 ∂μ) := by
  rw [(gaussian_freeTransport_entropy μ hμ hK t).2]
  have he (z:E×E) : ‖(freeTransport t z).1‖^2/2-‖z.1‖^2/2=
      t*⟪z.1,z.2⟫+(t^2/2)*‖z.2‖^2 := by
    change ‖z.1+t • z.2‖^2/2-‖z.1‖^2/2=_
    rw [norm_add_sq_real,real_inner_smul_right,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
    ring
  simp_rw [he]
  have hi1 := (integrable_inner_of_memLp_two hμ.fst hμ.snd).const_mul t
  have hi2 := hμ.snd.integrable_norm_pow'.const_mul (t^2/2)
  simp only [id_eq] at hi1 hi2
  rw [integral_add hi1 hi2,integral_const_mul,integral_const_mul]
  ring

theorem continuous_gaussian_freeTransport_entropy (μ:Measure (E×E)) [IsProbabilityMeasure μ]
    (hμ:MemLp id 2 μ)
    (hK:klDiv μ (gaussianPairProbability (E:=E):Measure (E×E))≠∞) :
    Continuous (fun t:ℝ=>(klDiv (transportJoint μ t)
      (gaussianPairProbability (E:=E):Measure (E×E))).toReal) := by
  simp_rw [gaussian_freeTransport_entropy_polynomial μ hμ hK]
  fun_prop

theorem continuous_freeTransport_conditional_entropy (μ:Measure (E×E)) [IsProbabilityMeasure μ]
    (hμ:MemLp id 2 μ)
    (hK:klDiv μ (gaussianPairProbability (E:=E):Measure (E×E))≠∞) :
    Continuous (fun t:ℝ=>(conditionalGaussianEntropy μ (stdGaussian E) t).toReal) := by
  apply SeqContinuous.continuous
  intro sn s hs
  have hw := (continuous_transportProbability μ).continuousAt.tendsto.comp hs
  have hent := (continuous_gaussian_freeTransport_entropy μ hμ hK).continuousAt.tendsto.comp hs
  have hh := gaussian_conditional_entropy_tendsto
    (fun k=>transportProbability μ (sn k)) (transportProbability μ s)
    (fun k=>(gaussian_freeTransport_entropy μ hμ hK (sn k)).1)
    (gaussian_freeTransport_entropy μ hμ hK s).1 hw hent
  simp only [conditionalGaussianEntropy,transportJoint_zero,transportPosition_zero] at hh
  change Tendsto (fun k=>(conditionalGaussianEntropy μ (stdGaussian E) (sn k)).toReal)
    atTop (𝓝 (conditionalGaussianEntropy μ (stdGaussian E) s).toReal) at hh
  exact hh

theorem continuous_freeTransport_boltzmann (μ:Measure (E×E)) [IsProbabilityMeasure μ]
    (hμ:MemLp id 2 μ)
    (hK:klDiv μ (gaussianPairProbability (E:=E):Measure (E×E))≠∞) :
    Continuous (fun t:ℝ=>boltzmannEntropy (transportPosition μ t)) := by
  have he (t:ℝ) : boltzmannEntropy (transportPosition μ t)=
      (klDiv μ (gaussianPairProbability (E:=E):Measure (E×E))).toReal-
      (∫z,‖z.1‖^2/2 ∂μ)-(Module.finrank ℝ E:ℝ)/2*Real.log (2*Real.pi)-
      (conditionalGaussianEntropy μ (stdGaussian E) t).toReal := by
    have hh := (gaussian_conditional_boltzmann_identity μ hμ hK t).2.2
    linarith
  simp_rw [he]
  exact continuous_const.sub (continuous_freeTransport_conditional_entropy μ hμ hK)

theorem A1.continuous_freeTransport_upper_rate {U:E→ℝ} {m L:ℝ} (a:A1 U m L)
    (μ:Measure (E×E)) [IsProbabilityMeasure μ] (hμ:MemLp id 2 μ)
    (hK:klDiv μ (phaseGibbs U)≠∞) :
    Continuous (fun s:ℝ=>6*(conditionalGaussianEntropy μ (stdGaussian E) s).toReal-
      (boltzmannEntropy (transportPosition μ s)-boltzmannEntropy (positionGibbs U))) := by
  have hG := a.phaseGaussian_entropy_finite μ hμ hK
  exact ((continuous_freeTransport_conditional_entropy μ hμ hG).const_mul 6).sub
    ((continuous_freeTransport_boltzmann μ hμ hG).sub continuous_const)

end PersistencePays
#print axioms PersistencePays.continuous_freeTransport_conditional_entropy
#print axioms PersistencePays.continuous_freeTransport_boltzmann
#print axioms PersistencePays.A1.continuous_freeTransport_upper_rate
