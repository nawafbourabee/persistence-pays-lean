import PersistencePays.GaussianStressIdentity
import PersistencePays.GaussianDensityGradient
import PersistencePays.GaussianCovarianceBounds

/-! Actual weighted covariance and divergence bounds required by static Lemma A.1. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal
universe u
variable {E Z:Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology Z]

lemma matrixDivergence_norm_le (S:E→E→L[ℝ]E) (y:E) :
    ‖matrixDivergence S y‖≤(Module.finrank ℝ E:ℝ)*‖fderiv ℝ S y‖ := by
  classical
  unfold matrixDivergence
  calc
    _≤∑ i,‖(fderiv ℝ S y (stdOrthonormalBasis ℝ E i)) (stdOrthonormalBasis ℝ E i)‖:=norm_sum_le _ _
    _≤∑ i,‖fderiv ℝ S y‖:=by
      apply Finset.sum_le_sum
      intro i _
      have h1:=(fderiv ℝ S y (stdOrthonormalBasis ℝ E i)).le_opNorm (stdOrthonormalBasis ℝ E i)
      have h2:=(fderiv ℝ S y).le_opNorm (stdOrthonormalBasis ℝ E i)
      simpa only [(stdOrthonormalBasis ℝ E).norm_eq_one,mul_one] using h1.trans
        (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
    _=_:=by simp

lemma gaussianRegressionCovariance_space_contDiff (μ:Measure Z) [IsProbabilityMeasure μ]
    (g:Z→E×E) (hg:Continuous g) {ε:ℝ} (hε:0<ε) (s:ℝ) :
    ContDiff ℝ 1 (gaussianRegressionCovariance μ g ε s) := by
  have hn:ContDiff ℝ 1 (gaussianFlightDensity μ g ε s):=
    (gaussianFlightDensity_contDiff 1 μ g hg hε.ne').comp (contDiff_const.prodMk contDiff_id)
  have he:gaussianRegressionCovariance μ g ε s=(fun y=>(gaussianFlightDensity μ g ε s y)⁻¹•
      gaussianFlightStress μ g ε s y) := by
    funext y
    unfold gaussianFlightStress
    rw [smul_smul,inv_mul_cancel₀ (gaussianFlightDensity_pos μ g hg hε s y).ne',one_smul]
  rw [he]
  exact (hn.inv (fun y=>(gaussianFlightDensity_pos μ g hg hε s y).ne')).smul
    (gaussianFlightStress_space_contDiff μ g hg hε s)

theorem gaussianFlightStress_bounds (μ:Measure Z) [IsProbabilityMeasure μ]
    (g:Z→E×E) (hg:Continuous g) {ε:ℝ} (hε:0<ε) (A B:ℝ≥0)
    (hA:∀s z,‖regressionLatentMean s (g z)‖≤A)
    (hB:∀s z,‖regressionScore ε s (g z)‖≤B) :
    ∃C:ℝ,0≤C ∧ ∀s y,
      ‖gaussianFlightStress μ g ε s y‖≤C*gaussianFlightDensity μ g ε s y ∧
      ‖matrixDivergence (gaussianFlightStress μ g ε s) y‖≤
        C*(1+‖y‖)*gaussianFlightDensity μ g ε s y := by
  let Cs:ℝ:=2*(A:ℝ)^2+ε^2
  let K:ℝ:=6*(A:ℝ)^2*B
  let d:ℝ:=Module.finrank ℝ E
  let C:ℝ:=Cs+d*K+Cs*((ε^2)⁻¹+B)
  have hCs:0≤Cs:=by dsimp [Cs]; positivity
  have hK:0≤K:=by dsimp [K]; positivity
  have hd:0≤d:=by dsimp [d]; positivity
  have hC:0≤C:=by dsimp [C]; positivity
  have hCsC:Cs≤C:=by
    dsimp [C]
    exact (le_add_of_nonneg_right (mul_nonneg hd hK)).trans
      (le_add_of_nonneg_right (mul_nonneg hCs (add_nonneg (by positivity : 0≤(ε^2)⁻¹) B.property)))
  refine ⟨C,hC,?_⟩
  intro s y
  have hn:0≤gaussianFlightDensity μ g ε s y:=(gaussianFlightDensity_pos μ g hg hε s y).le
  have hnb:ContDiff ℝ 1 (gaussianFlightDensity μ g ε s):=
    (gaussianFlightDensity_contDiff 1 μ g hg hε.ne').comp (contDiff_const.prodMk contDiff_id)
  have hS:=gaussianRegressionCovariance_space_contDiff μ g hg hε s
  have hbound:=gaussianRegressionCovariance_bounds μ g hg hε.ne' A B hA hB s y
  have hgrad:=gaussianFlightDensity_gradient_bound μ g hg hε s (hB s) y
  constructor
  · unfold gaussianFlightStress
    rw [norm_smul,Real.norm_of_nonneg hn]
    calc
      _≤gaussianFlightDensity μ g ε s y*Cs:=mul_le_mul_of_nonneg_left hbound.1 hn
      _≤gaussianFlightDensity μ g ε s y*C:=mul_le_mul_of_nonneg_left hCsC hn
      _=_:=mul_comm _ _
  · have hdiv:‖matrixDivergence (gaussianRegressionCovariance μ g ε s) y‖≤d*K:=
      (matrixDivergence_norm_le _ y).trans (mul_le_mul_of_nonneg_left hbound.2 hd)
    change ‖matrixDivergence (fun y=>gaussianFlightDensity μ g ε s y•
      gaussianRegressionCovariance μ g ε s y) y‖≤_
    rw [matrixDivergence_smul hnb hS]
    have hh:‖gaussianFlightDensity μ g ε s y•matrixDivergence (gaussianRegressionCovariance μ g ε s) y+
        gaussianRegressionCovariance μ g ε s y (gradient (gaussianFlightDensity μ g ε s) y)‖≤
        gaussianFlightDensity μ g ε s y*(d*K+Cs*((ε^2)⁻¹*‖y‖+B)) := by
      calc
        _≤‖gaussianFlightDensity μ g ε s y•matrixDivergence (gaussianRegressionCovariance μ g ε s) y‖+
          ‖gaussianRegressionCovariance μ g ε s y (gradient (gaussianFlightDensity μ g ε s) y)‖:=norm_add_le _ _
        _≤gaussianFlightDensity μ g ε s y*(d*K)+Cs*(gaussianFlightDensity μ g ε s y*((ε^2)⁻¹*‖y‖+B)):=by
          apply add_le_add
          · rw [norm_smul,Real.norm_of_nonneg hn]
            exact mul_le_mul_of_nonneg_left hdiv hn
          · apply ((gaussianRegressionCovariance μ g ε s y).le_opNorm _).trans
            exact mul_le_mul hbound.1 hgrad (norm_nonneg _) hCs
        _=_:=by ring
    apply hh.trans
    have hc:d*K+Cs*((ε^2)⁻¹*‖y‖+B)≤C*(1+‖y‖) := by
      dsimp [C]
      nlinarith [mul_nonneg hCs (norm_nonneg y),mul_nonneg (mul_nonneg hd hK) (norm_nonneg y),
        mul_nonneg (mul_nonneg hCs B.property) (norm_nonneg y),mul_nonneg hCs (by positivity : 0≤(ε^2)⁻¹)]
    nlinarith [mul_le_mul_of_nonneg_right hc hn]

end PersistencePays
#print axioms PersistencePays.gaussianFlightStress_bounds
