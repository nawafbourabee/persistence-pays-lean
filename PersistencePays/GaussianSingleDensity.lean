import PersistencePays.IsotropicObservation
import PersistencePays.GaussianMeanField

/-! Explicit smooth densities for each Gaussian free-flight component. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def flightResidual (s:ℝ) (y:E) (z:E×E):E := y-latentCenter s z

def singleFlightLog (ε s:ℝ) (y:E) (z:E×E):ℝ :=
  -((Module.finrank ℝ E:ℝ)/2)*Real.log (1+s^2)
    -‖flightResidual s y z‖^2/(2*ε^2*(1+s^2))

def singleFlightDensity (ε s:ℝ) (y:E) (z:E×E):ℝ :=
  heatConstant E 1 * ε⁻¹^Module.finrank ℝ E * Real.exp (singleFlightLog ε s y z)

lemma singleFlightDensity_pos {ε:ℝ} (hε:0<ε) (s:ℝ) (y:E) (z:E×E) :
    0<singleFlightDensity ε s y z := by
  exact mul_pos (mul_pos (heatConstant_pos (by norm_num)) (pow_pos (inv_pos.mpr hε) _))
    (Real.exp_pos _)

lemma isotropicScale_det (σ:ℝ) (hσ:σ≠0) :
    LinearMap.det (isotropicScale (E:=E) σ hσ).toLinearMap=σ^Module.finrank ℝ E := by
  have he:(isotropicScale (E:=E) σ hσ).toLinearMap=σ•LinearMap.id := by ext x; rfl
  rw [he,LinearMap.det_smul,LinearMap.det_id,mul_one]

lemma exp_log_dimension (s:ℝ) (d:ℕ) :
    Real.exp (-((d:ℝ)/2)*Real.log (1+s^2))=(Real.sqrt (1+s^2))⁻¹^d := by
  have hd:0<1+s^2 := by positivity
  have hs:0<Real.sqrt (1+s^2) := Real.sqrt_pos.mpr hd
  rw [show -((d:ℝ)/2)*Real.log (1+s^2)=(d:ℝ)*(-Real.log (Real.sqrt (1+s^2))) by
    rw [Real.log_sqrt hd.le]; ring,
    Real.exp_nat_mul,Real.exp_neg,Real.exp_log hs]

lemma singleFlightDensity_eq_gaussian {ε:ℝ} (hε:0<ε) (s:ℝ) (y:E) (z:E×E) :
    ENNReal.ofReal (singleFlightDensity ε s y z)=
      affineGaussianDensity (isotropicScale (observationNoise ε s)
        (observationNoise_pos hε s).ne') (latentCenter s z) y := by
  have ho:=observationNoise_pos hε s
  have hd:0<1+s^2 := by positivity
  have hs:0<Real.sqrt (1+s^2) := Real.sqrt_pos.mpr hd
  have hj:inverseJacobian (isotropicScale (E:=E) (observationNoise ε s) ho.ne')=
      ENNReal.ofReal ((observationNoise ε s)⁻¹^Module.finrank ℝ E) := by
    unfold inverseJacobian
    rw [isotropicScale_det,abs_of_pos (inv_pos.mpr (pow_pos ho _)),inv_pow]
  rw [affineGaussianDensity,ellipticHeat,hj,heatDensity,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  unfold singleFlightDensity singleFlightLog heatReal flightResidual
  rw [Real.exp_sub,exp_log_dimension]
  simp only [isotropicScale_symm_apply,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  have hs2:=Real.sq_sqrt hd.le
  have hexp:‖y-latentCenter s z‖^2/(2*ε^2*(1+s^2))=
      (observationNoise ε s)⁻¹^2*‖y-latentCenter s z‖^2/(2*1) := by
    unfold observationNoise
    field_simp [hε.ne',hs.ne',hd.ne']
    nlinarith [hs2]
  rw [hexp,neg_div,Real.exp_neg]
  unfold observationNoise
  rw [mul_inv_rev,mul_pow]
  ring

theorem singleFlightLog_contDiff (n:ℕ) {ε:ℝ} (hε:ε≠0) :
    ContDiff ℝ n (fun p:(ℝ×E)×(E×E)=>singleFlightLog ε p.1.1 p.1.2 p.2) := by
  unfold singleFlightLog flightResidual latentCenter
  apply ContDiff.sub
  · apply ContDiff.mul contDiff_const
    exact (contDiff_const.add (contDiff_fst.fst.pow 2)).log (fun p=>by positivity)
  · apply ContDiff.div
    · exact (contDiff_fst.snd.sub (contDiff_snd.fst.add
        (contDiff_fst.fst.smul contDiff_snd.snd))).norm_sq ℝ
    · fun_prop
    · intro p; exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hε)) (by positivity)

theorem singleFlightDensity_contDiff (n:ℕ) {ε:ℝ} (hε:ε≠0) :
    ContDiff ℝ n (fun p:(ℝ×E)×(E×E)=>singleFlightDensity ε p.1.1 p.1.2 p.2) :=
  contDiff_const.mul ((singleFlightLog_contDiff n hε).exp)

end PersistencePays
#print axioms PersistencePays.singleFlightDensity_eq_gaussian
#print axioms PersistencePays.singleFlightDensity_contDiff
