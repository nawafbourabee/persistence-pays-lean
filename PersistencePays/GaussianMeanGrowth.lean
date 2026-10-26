import PersistencePays.GaussianRemainderGrowth
import Mathlib.Analysis.Normed.Operator.Mul

noncomputable section
namespace PersistencePays
open MeasureTheory Set
universe u
variable {E Z:Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology Z]
local instance gaussianMeanGrowthInst1 : NormedAddCommGroup (ℝ×E) := inferInstance
local instance gaussianMeanGrowthInst2 : NormedSpace ℝ (ℝ×E) := inferInstance
local instance gaussianMeanGrowthInst3 : NormedAddCommGroup (ℝ×E→L[ℝ]E) := inferInstance

theorem gaussianMeanField_joint_growth (μ:Measure Z) [IsProbabilityMeasure μ]
    (g:Z→E×E) (hg:Continuous g) {ε:ℝ} (hε:ε≠0) (a b:ℝ) :
    ∃ C:ℝ, 1≤C ∧ ∀s∈Icc a b,∀y:E,
      ‖gaussianMeanField μ g ε s y‖≤C*(1+‖y‖) ∧
      ‖fderiv ℝ (gaussianMeanField μ g ε).uncurry (s,y)‖≤C*(1+‖y‖) ∧
      ‖fderiv ℝ (fderiv ℝ (gaussianMeanField μ g ε).uncurry) (s,y)‖≤C*(1+‖y‖)^2 := by
  obtain ⟨A,hA,bA⟩:=gaussianMeanRemainder_joint_growth μ g hg hε a b
  have hβ3:ContDiff ℝ 3 (fun p:ℝ×ℝ=>regressionBeta p.1):=
    contDiff_fst.div (contDiff_const.add (contDiff_fst.pow 2)) (fun p=>by positivity)
  obtain ⟨B,hB,bB⟩:=compact_coefficient_c2_bounds hβ3 (fun _:Unit=>(0:ℝ)) continuous_const a b
  have hβ:ContDiff ℝ 2 regressionBeta:=
    contDiff_id.div (contDiff_const.add (contDiff_id.pow 2)) (fun p=>by positivity)
  let S:ℝ→L[ℝ]E→L[ℝ]E:=ContinuousLinearMap.lsmul ℝ ℝ
  let L:ℝ×E→E:=fun p=>regressionBeta p.1•p.2
  let R:ℝ×E→E:=(gaussianMeanRemainder μ g ε).uncurry
  have hL:ContDiff ℝ 2 L:=(hβ.comp contDiff_fst).smul contDiff_snd
  have hR:ContDiff ℝ 2 R:=gaussianMeanRemainder_contDiff 2 μ g hg hε
  have hdL:Differentiable ℝ L:=hL.differentiable (by norm_num)
  have hdR:Differentiable ℝ R:=hR.differentiable (by norm_num)
  have hddL:Differentiable ℝ (fderiv ℝ L):=(hL.fderiv_right (m:=1) (by norm_num)).differentiable (by norm_num)
  have hddR:Differentiable ℝ (fderiv ℝ R):=(hR.fderiv_right (m:=1) (by norm_num)).differentiable (by norm_num)
  have heq:(gaussianMeanField μ g ε).uncurry=L+R:=rfl
  have hdeq:fderiv ℝ (L+R)=fderiv ℝ L+fderiv ℝ R:=by
    funext p
    exact fderiv_add (hdL p) (hdR p)
  let C:ℝ:=1+B+A+2*‖S‖*B
  have hC:1≤C:=by dsimp [C]; nlinarith [mul_nonneg (norm_nonneg S) hB.le]
  refine ⟨C,hC,?_⟩
  intro s hs y
  have ba:=bA s hs y
  have bb:=bB s hs ()
  have bl:=affine_time_derivative_bounds S hβ (s,y) hB.le bb.1 bb.2.1 bb.2.2
  have bw:0≤1+‖y‖:=by positivity
  have bw2:1+‖y‖≤(1+‖y‖)^2:=by nlinarith [norm_nonneg y,sq_nonneg ‖y‖]
  have hSB:0≤‖S‖*B:=mul_nonneg (norm_nonneg S) hB.le
  have h0C:B+A≤C:=by dsimp [C]; linarith
  have h1C:‖S‖*B+A≤C:=by dsimp [C]; linarith
  have h2C:2*‖S‖*B+A≤C:=by dsimp [C]; linarith
  refine ⟨?_,?_,?_⟩
  · calc
      _ ≤ ‖regressionBeta s•y‖+‖gaussianMeanRemainder μ g ε s y‖:=norm_add_le _ _
      _ = ‖regressionBeta s‖*‖y‖+‖gaussianMeanRemainder μ g ε s y‖:=by rw [norm_smul]
      _ ≤ B*‖y‖+A:=add_le_add (mul_le_mul_of_nonneg_right bb.1 (norm_nonneg y)) ba.1
      _ ≤ (B+A)*(1+‖y‖):=by nlinarith [mul_nonneg (by linarith : 0≤A) (norm_nonneg y)]
      _ ≤ C*(1+‖y‖):=mul_le_mul_of_nonneg_right h0C bw
  · rw [heq,fderiv_add (hdL _) (hdR _)]
    calc
      _ ≤ ‖fderiv ℝ L (s,y)‖+‖fderiv ℝ R (s,y)‖:=norm_add_le _ _
      _ ≤ ‖S‖*B*(1+‖y‖)+A*(1+‖y‖):=add_le_add bl.1 ba.2.1
      _ = (‖S‖*B+A)*(1+‖y‖):=by ring
      _ ≤ _:=mul_le_mul_of_nonneg_right h1C bw
  · rw [heq,hdeq,fderiv_add (hddL _) (hddR _)]
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ L) (s,y)‖+‖fderiv ℝ (fderiv ℝ R) (s,y)‖:=by
        convert norm_add_le (fderiv ℝ (fderiv ℝ L) (s,y)) (fderiv ℝ (fderiv ℝ R) (s,y)) using 1
      _ ≤ 2*‖S‖*B*(1+‖y‖)+A*(1+‖y‖)^2:=add_le_add bl.2 ba.2.2
      _ ≤ 2*‖S‖*B*(1+‖y‖)^2+A*(1+‖y‖)^2:=by gcongr
      _ = (2*‖S‖*B+A)*(1+‖y‖)^2:=by ring
      _ ≤ _:=mul_le_mul_of_nonneg_right h2C (sq_nonneg _)
end PersistencePays
#print axioms PersistencePays.gaussianMeanField_joint_growth
