import PersistencePays.GaussianLatentDefs
import PersistencePays.CompactPosteriorSmooth
import PersistencePays.AffinePosteriorSecondBound
import PersistencePays.VariationalFlowExistence
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The smooth conditional-mean formula for a compact latent Gaussian mixture.
The separate Gaussian-regression law identifies this formula with condKernel. -/
noncomputable section
namespace PersistencePays
open MeasureTheory Set
open scoped InnerProductSpace NNReal
universe u
variable {E Z:Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology Z]

def gaussianMeanRemainder (μ:Measure Z) (g:Z→E×E) (ε s:ℝ) (y:E):E :=
  affinePosteriorMean μ (fun z=>regressionLatentMean s (g z))
    (fun z=>regressionScore ε s (g z)) (fun z=>regressionLogWeight ε s (g z)) y

def gaussianMeanField (μ:Measure Z) (g:Z→E×E) (ε s:ℝ) (y:E):E :=
  regressionBeta s • y+gaussianMeanRemainder μ g ε s y

theorem regressionLatentMean_contDiff (n:ℕ) :
    ContDiff ℝ n (fun p:ℝ×(E×E)=>regressionLatentMean p.1 p.2) := by
  unfold regressionLatentMean
  apply ContDiff.smul
  · apply ContDiff.inv
    · fun_prop
    · intro x; positivity
  · fun_prop

theorem regressionScore_contDiff (n:ℕ) {ε:ℝ} (hε:ε≠0) :
    ContDiff ℝ n (fun p:ℝ×(E×E)=>regressionScore ε p.1 p.2) := by
  unfold regressionScore latentCenter
  apply ContDiff.smul
  · apply ContDiff.inv
    · fun_prop
    · intro x; exact mul_ne_zero (pow_ne_zero _ hε) (by positivity)
  · fun_prop

theorem regressionLogWeight_contDiff (n:ℕ) {ε:ℝ} (hε:ε≠0) :
    ContDiff ℝ n (fun p:ℝ×(E×E)=>regressionLogWeight ε p.1 p.2) := by
  unfold regressionLogWeight latentCenter
  apply ContDiff.div
  · exact (((contDiff_snd.fst : ContDiff ℝ n (fun p:ℝ×(E×E)=>p.2.1)).add (contDiff_fst.smul contDiff_snd.snd)).norm_sq ℝ).neg
  · fun_prop
  · intro x
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hε)) (by positivity)

theorem gaussianMeanRemainder_contDiff (n:ℕ) (μ:Measure Z) [IsProbabilityMeasure μ]
    (g:Z→E×E) (hg:Continuous g) {ε:ℝ} (hε:ε≠0) :
    ContDiff ℝ n (gaussianMeanRemainder μ g ε).uncurry := by
  let ψ:((ℝ×E)×(E×E))→ℝ:=fun p=>regressionExponent ε p.1.1 (p.1.2,p.2)
  let F:((ℝ×E)×(E×E))→E:=fun p=>regressionLatentMean p.1.1 p.2
  have hproj:ContDiff ℝ n (fun p:((ℝ×E)×(E×E))=>(p.1.1,p.2)) :=
    contDiff_fst.fst.prodMk contDiff_snd
  have hψ:ContDiff ℝ n ψ :=
    (((regressionScore_contDiff n hε).comp hproj).inner ℝ contDiff_fst.snd).add
      ((regressionLogWeight_contDiff n hε).comp hproj)
  have hF:ContDiff ℝ n F := (regressionLatentMean_contDiff n).comp hproj
  exact compactPosteriorMean_contDiff n μ g hg ψ hψ F hF

theorem gaussianMeanField_contDiff (n:ℕ) (μ:Measure Z) [IsProbabilityMeasure μ]
    (g:Z→E×E) (hg:Continuous g) {ε:ℝ} (hε:ε≠0) :
    ContDiff ℝ n (gaussianMeanField μ g ε).uncurry := by
  have hβ:ContDiff ℝ n (fun p:ℝ×E=>regressionBeta p.1) :=
    contDiff_fst.div (contDiff_const.add (contDiff_fst.pow 2)) (fun p=>by positivity)
  exact (hβ.smul contDiff_snd).add (gaussianMeanRemainder_contDiff n μ g hg hε)

theorem regressionLatentMean_norm_bound {R:ℝ} (hR:0≤R) (s:ℝ) (z:E×E)
    (hx:‖z.1‖≤R) (hv:‖z.2‖≤R) : ‖regressionLatentMean s z‖≤2*R := by
  have hd:0<1+s^2 := by positivity
  have ha:1+|s|≤2*(1+s^2) := by nlinarith [sq_nonneg (|s|-1),sq_abs s,sq_nonneg s]
  unfold regressionLatentMean
  rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hd.le)]
  have hn:‖z.2-s•z.1‖≤R*(1+|s|) := by
    calc
      _ ≤ ‖z.2‖+‖s•z.1‖ := norm_sub_le _ _
      _ = ‖z.2‖+|s| *‖z.1‖ := by rw [norm_smul,Real.norm_eq_abs]
      _ ≤ R+|s| *R := add_le_add hv (mul_le_mul_of_nonneg_left hx (abs_nonneg _))
      _ = _ := by ring
  apply (inv_mul_le_iff₀ hd).mpr
  nlinarith [mul_le_mul_of_nonneg_left ha hR]

theorem regressionScore_norm_bound {R ε:ℝ} (hR:0≤R) (hε:ε≠0) (s:ℝ) (z:E×E)
    (hx:‖z.1‖≤R) (hv:‖z.2‖≤R) : ‖regressionScore ε s z‖≤2*R/ε^2 := by
  have hd:0<ε^2*(1+s^2) := mul_pos (sq_pos_of_ne_zero hε) (by positivity)
  have ha:1+|s|≤2*(1+s^2) := by nlinarith [sq_nonneg (|s|-1),sq_abs s,sq_nonneg s]
  have hn:‖latentCenter s z‖≤R*(1+|s|) := by
    calc
      _ ≤ ‖z.1‖+‖s•z.2‖ := norm_add_le _ _
      _ = ‖z.1‖+|s| *‖z.2‖ := by rw [norm_smul,Real.norm_eq_abs]
      _ ≤ R+|s| *R := add_le_add hx (mul_le_mul_of_nonneg_left hv (abs_nonneg _))
      _ = _ := by ring
  unfold regressionScore
  rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hd.le)]
  apply (inv_mul_le_iff₀ hd).mpr
  have heq:(ε^2*(1+s^2))*(2*R/ε^2)=2*R*(1+s^2) := by field_simp
  rw [heq]
  nlinarith [mul_le_mul_of_nonneg_left ha hR]

end PersistencePays
#print axioms PersistencePays.gaussianMeanField_contDiff
#print axioms PersistencePays.regressionScore_norm_bound
