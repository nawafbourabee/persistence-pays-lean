import PersistencePays.TheoremTwoParameters

/-! Theorem 2 with a finite-entropy initial law: the exact numerical rate and
all second/third moment remainders for the actual unadjusted chain. The only
remaining analytic premise is the explicitly named smooth free-flight theorem. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem A1.unadjustedEntropyLaw_memLp {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] {p : ℝ≥0∞} (hp : p ≠ ∞) (hμ : MemLp id p μ)
    (h r σ : ℝ) (n : ℕ) : MemLp id p (unadjustedEntropyLaw a h r σ μ n) := by
  induction n with
  | zero => simpa only [unadjustedEntropyLaw_zero] using hμ
  | succ n ih =>
    rw [unadjustedEntropyLaw_succ]
    exact a.unadjusted_step_memLp _ p hp ih h r σ

def unadjustedFlightMoment {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (h r σ : ℝ) (μ : Measure (E×E)) (k p : ℕ) : ℝ :=
  ∫ z,‖flightVelocity (gradient U) h z‖^p ∂phaseOUKernel r σ ∘ₘ unadjustedEntropyLaw a h r σ μ k

def theoremTwoMomentBound {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (LH h r σ rate : ℝ) (μ : Measure (E×E)) (n : ℕ) : ℝ :=
  finiteMaxNonnegative (fun k => LH*h^2/(12*rate)*unadjustedFlightMoment a h r σ μ k 3+
    221/(16*r)*(L*h^2)*unadjustedFlightMoment a h r σ μ k 2) n

theorem A1.theorem_two_finite_entropy {U : E → ℝ} {m L LH : ℝ} (a : A1 U m L)
    (a2 : A2 U LH) (hsm : GaussianSmoothedFreeTransportBound a)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 3 μ)
    (hK : klDiv μ (phaseGibbs U) ≠ ∞) (h : ℝ) (hh : 0 < h)
    (hhmax : Real.sqrt m*h ≤ 3/16) (n : ℕ) :
    let r := Real.exp (-(Real.sqrt m*h))
    let σ := Real.sqrt (1-Real.exp (-2*(Real.sqrt m*h)))
    let rate := r^2*Real.sqrt m/(4*(16+r))
    let p := unadjustedEntropyLaw a h r σ μ
    (klDiv (p n) (phaseGibbs U)).toReal ≤
      (17/15:ℝ)*Real.exp (-rate*h*(n:ℝ))*(klDiv μ (phaseGibbs U)).toReal+
        (16/15:ℝ)*(h^2*L/4*(∫ z,U z.1-U a.minimizer ∂p n)+
          theoremTwoMomentBound a LH h r σ rate μ n) := by
  let t := Real.sqrt m*h
  let r := Real.exp (-t)
  let σ := Real.sqrt (1-Real.exp (-2*t))
  let θ := r/16
  let rate := r^2*Real.sqrt m/(4*(16+r))
  let p := unadjustedEntropyLaw a h r σ μ
  let M := theoremTwoMomentBound a LH h r σ rate μ n
  have ht : 0 < t := mul_pos (Real.sqrt_pos.mpr a.m_pos) hh
  obtain ⟨hθ,hθu,hc1,hc2,hc3,hrate,hrh,hrh1,hcompare,hrecip,hcoef,_⟩ :=
    theorem_two_parameters m h a.m_pos hh hhmax
  obtain ⟨hr,hr1,hσ,hn,_,_,_,_⟩ := normalized_ou_coefficients t ht.le
  have hrp : 0 < r := hr
  have hratep : 0 < rate := (mul_pos_iff_of_pos_right hh).mp hrh
  have hM : 0 ≤ M := finiteMaxNonnegative_nonneg _ _
  have hμ2 : MemLp id 2 μ := hμ.mono_exponent (by norm_num)
  have hp3 (k : ℕ) : MemLp id 3 (p k) := a.unadjustedEntropyLaw_memLp μ (by norm_num) hμ h r σ k
  have hp2 (k : ℕ) : MemLp id 2 (p k) := (hp3 k).mono_exponent (by norm_num)
  have hdef (k : ℕ) (hk : k<n) : unadjustedEntropyDefect a h r σ θ μ k ≤ rate*h*M := by
    let ν := phaseOUKernel r σ ∘ₘ p k
    have hν3 := phaseOUKernel_memLp (p k) 3 (by norm_num) (hp3 k) r σ
    have he := a.expectedVerletRemainder_bound a2 ν hν3 h hh.le
    have hQ : 0 ≤ unadjustedFlightMoment a h r σ μ k 2 := integral_nonneg (fun _ => sq_nonneg _)
    have hc : θ*Real.sqrt m*(13/4:ℝ) ≤ rate*(221/(16*r)) := by
      have hc' : (θ*Real.sqrt m*(13/4:ℝ))/rate ≤ 221/(16*r) := by
        change (θ*Real.sqrt m/rate)*(13/4:ℝ) ≤ 221/(16*r) at hcoef
        convert hcoef using 1 <;> ring
      have hc'' := (div_le_iff₀ hratep).mp hc'
      nlinarith
    have hcm := mul_le_mul_of_nonneg_right hc
      (show 0 ≤ h*(L*h^2)*unadjustedFlightMoment a h r σ μ k 2 by positivity [a.L_pos])
    have hbound := mul_le_mul_of_nonneg_left
      (le_finiteMaxNonnegative (fun j => LH*h^2/(12*rate)*unadjustedFlightMoment a h r σ μ j 3+
        221/(16*r)*(L*h^2)*unadjustedFlightMoment a h r σ μ j 2) hk) hrh.le
    have hid : rate*h*(LH*h^2/(12*rate)*unadjustedFlightMoment a h r σ μ k 3) =
        LH/12*h^3*unadjustedFlightMoment a h r σ μ k 3 := by field_simp [hratep.ne'] <;> ring
    change expectedVerletRemainder U h ν ≤ LH/12*h^3*unadjustedFlightMoment a h r σ μ k 3 at he
    change unadjustedEntropyDefect a h r σ θ μ k ≤ rate*h*M
    dsimp only [unadjustedEntropyDefect]
    change expectedVerletRemainder U h ν+
      θ*Real.sqrt m*h*((13/4:ℝ)*L*h^2*unadjustedFlightMoment a h r σ μ k 2) ≤ rate*h*M
    change rate*h*(LH*h^2/(12*rate)*unadjustedFlightMoment a h r σ μ k 3+
      221/(16*r)*(L*h^2)*unadjustedFlightMoment a h r σ μ k 2) ≤ rate*h*M at hbound
    rw [mul_add,hid] at hbound
    nlinarith
  have hb := a.unadjusted_entropy_bound_up_to hsm μ hμ2 hK r σ h θ rate (rate*h*M)
    hrp.le hσ hn hh hθ.le (by change θ ≤ 1/16 at hθu; linarith) hc1 hc2 hc3 hrate hrh hrh1
    (mul_nonneg hrh.le hM) n hdef
  have hcorr := a.expectedGradientCorrection_bounds (p n) (hp2 n) h
  have hg : 0 ≤ expectedGradientCorrection U h (p n)+M := add_nonneg hcorr.1 hM
  have hratio := mul_le_mul_of_nonneg_right hrecip hg
  have hinit := mul_le_mul_of_nonneg_right hcompare
    (mul_nonneg (Real.exp_nonneg (-rate*h*(n:ℝ)))
      (show 0 ≤ (klDiv μ (phaseGibbs U)).toReal from ENNReal.toReal_nonneg))
  have hfinal := mul_le_mul_of_nonneg_left hcorr.2 (show 0 ≤ (16/15:ℝ) by norm_num)
  have hdiv : rate*h*M/(rate*h)=M := by field_simp [hratep.ne',hh.ne']
  rw [hdiv] at hb
  change (klDiv (p n) (phaseGibbs U)).toReal ≤ _ at hb ⊢
  change 1/(1-θ)*(expectedGradientCorrection U h (p n)+M) ≤
    (16/15:ℝ)*(expectedGradientCorrection U h (p n)+M) at hratio
  change (1+θ)/(1-θ)*(Real.exp (-rate*h*(n:ℝ))*(klDiv μ (phaseGibbs U)).toReal) ≤
    (17/15:ℝ)*(Real.exp (-rate*h*(n:ℝ))*(klDiv μ (phaseGibbs U)).toReal) at hinit
  change (klDiv (p n) (phaseGibbs U)).toReal ≤
    (1+θ)/(1-θ)*Real.exp (-rate*h*(n:ℝ))*(klDiv μ (phaseGibbs U)).toReal+
    (expectedGradientCorrection U h (p n)+M)/(1-θ) at hb
  rw [div_eq_mul_inv] at hratio
  rw [div_eq_mul_inv (expectedGradientCorrection U h (p n)+M)] at hb
  simp only [one_mul] at hratio
  change (klDiv (p n) (phaseGibbs U)).toReal ≤
    (17/15:ℝ)*Real.exp (-rate*h*(n:ℝ))*(klDiv μ (phaseGibbs U)).toReal+
      (16/15:ℝ)*(h^2*L/4*(∫ z,U z.1-U a.minimizer ∂p n)+M)
  nlinarith

end PersistencePays
#print axioms PersistencePays.A1.theorem_two_finite_entropy
