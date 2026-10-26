import PersistencePays.ComparisonEntropyIteration
import PersistencePays.SectionSixConstants

/-! Proposition 5.10 for the actual comparison iterates, with explicit uniform
bounds on the literal defects. The smooth free-flight theorem is the sole
unresolved analytic premise. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem A1.comparison_entropy_decay {U:E→ℝ} {L h:ℝ} (a:A1 U 1 L)
    (hsm:GaussianSmoothedFreeTransportBound a) (hstar:a.minimizer=0) (hzero:U 0=0)
    (hh:0<h) (hmax:h≤1/8) (hL:L*h^2≤1/2)
    (μ:Measure (E×E)) [IsProbabilityMeasure μ] (hμ:MemLp id 2 μ)
    (hK:klDiv μ (phaseGibbs U)≠∞) (D vstar T B:ℝ)
    (hD:0<D) (hT:0≤T) (hB:0≤B) (n:ℕ)
    (hcap:∀k,k<n → phaseOUKernel (Real.exp (-h)) (Real.sqrt (1-Real.exp (-2*h))) ∘ₘ
      comparisonEntropyLaw a h (Real.exp (-h)) (Real.sqrt (1-Real.exp (-2*h))) vstar μ k≤
        ENNReal.ofReal D • ((volume:Measure E).prod volume))
    (hα:∀k,k<n → ((phaseOUKernel (Real.exp (-h)) (Real.sqrt (1-Real.exp (-2*h))) ∘ₘ
      comparisonEntropyLaw a h (Real.exp (-h)) (Real.sqrt (1-Real.exp (-2*h))) vstar μ k)
      {z|vstar<‖flightVelocity (gradient U) h z‖}).toReal<1)
    (hTbound:∀k,k<n → expectedComparisonRemainder U h vstar
      (phaseOUKernel (Real.exp (-h)) (Real.sqrt (1-Real.exp (-2*h))) ∘ₘ
        comparisonEntropyLaw a h (Real.exp (-h)) (Real.sqrt (1-Real.exp (-2*h))) vstar μ k)≤T)
    (hBbound:∀k,k<n → a.comparisonCorrectorError
      (phaseOUKernel (Real.exp (-h)) (Real.sqrt (1-Real.exp (-2*h))) ∘ₘ
        comparisonEntropyLaw a h (Real.exp (-h)) (Real.sqrt (1-Real.exp (-2*h))) vstar μ k) h D vstar≤B) :
    let r:=Real.exp (-h)
    let σ:=Real.sqrt (1-Real.exp (-2*h))
    let rate:=r^2/(4*(16+r))
    let p:=comparisonEntropyLaw a h r σ vstar μ
    (klDiv (p n) (phaseGibbs U)).toReal≤
      (17/15:ℝ)*Real.exp (-rate*h*(n:ℝ))*(klDiv μ (phaseGibbs U)).toReal+
      (16/15:ℝ)*(h^2*L/4*(∫z,U z.1∂p n)+T/(rate*h)+(4.79:ℝ)*B) := by
  let r:=Real.exp (-h)
  let σ:=Real.sqrt (1-Real.exp (-2*h))
  let θ:=r/16
  let rate:=r^2/(4*(16+r))
  let p:=comparisonEntropyLaw a h r σ vstar μ
  obtain ⟨hθ,hθu,hc1,hc2,hc3,hrate,_,hrh,hrh1,hcompare,hrecip,_⟩ :=
    theorem_two_normalized_parameters h hh (by linarith)
  obtain ⟨hr,_,hσ,hn,_,_,_,_⟩ := normalized_ou_coefficients h hh.le
  have hratep:0<rate := (mul_pos_iff_of_pos_right hh).mp hrh
  have hM:0≤T+θ*h*B := by positivity
  have hdef (k:ℕ) (hk:k<n) : comparisonEntropyDefect a h r σ θ D vstar μ k≤T+θ*h*B := by
    exact add_le_add (hTbound k hk) (mul_le_mul_of_nonneg_left (hBbound k hk) (by positivity))
  have hb:=a.comparison_entropy_bound_up_to hsm hstar hzero μ hμ hK r σ h θ D vstar rate
    (T+θ*h*B) hr.le hσ hn hh hL hD hθ.le (by change θ≤1/16 at hθu; linarith)
    hc1 hc2 hc3 hrate.symm hrh hrh1 hM n hcap hα hdef
  have hp2 : MemLp id 2 (p n) := a.comparison_iterates_memLp μ 2 (by norm_num) hμ h vstar r σ n
  have hcorr:=a.expectedGradientCorrection_bounds (p n) hp2 h
  have hcorr' : expectedGradientCorrection U h (p n)≤h^2*L/4*(∫z,U z.1∂p n) := by
    simpa only [hstar,hzero,sub_zero] using hcorr.2
  have he:θ/rate=(16+r)/(4*r) := by dsimp [θ,rate]; field_simp [(Real.exp_pos (-h)).ne']; ring
  have hratio:θ/rate≤(4.79:ℝ) := by rw [he]; exact (comparison_entropy_rate_constants hh hmax).2.2
  have hMdiv: (T+θ*h*B)/(rate*h)≤T/(rate*h)+(4.79:ℝ)*B := by
    have heq : (T+θ*h*B)/(rate*h)=T/(rate*h)+(θ/rate)*B := by
      field_simp [hratep.ne',hh.ne'] <;> ring
    rw [heq]
    exact add_le_add_right (mul_le_mul_of_nonneg_right hratio hB) _
  have hnonneg:0≤expectedGradientCorrection U h (p n)+(T+θ*h*B)/(rate*h) :=
    add_nonneg hcorr.1 (div_nonneg hM hrh.le)
  have hfinal:=mul_le_mul_of_nonneg_right hrecip hnonneg
  have hinit:=mul_le_mul_of_nonneg_right hcompare
    (mul_nonneg (Real.exp_nonneg (-rate*h*(n:ℝ)))
      (show 0≤(klDiv μ (phaseGibbs U)).toReal from ENNReal.toReal_nonneg))
  change (klDiv (p n) (phaseGibbs U)).toReal≤_ at hb ⊢
  change (1+θ)/(1-θ)*(Real.exp (-rate*h*(n:ℝ))*(klDiv μ (phaseGibbs U)).toReal)≤
    (17/15:ℝ)*(Real.exp (-rate*h*(n:ℝ))*(klDiv μ (phaseGibbs U)).toReal) at hinit
  change 1/(1-θ)*(expectedGradientCorrection U h (p n)+(T+θ*h*B)/(rate*h))≤
    (16/15:ℝ)*(expectedGradientCorrection U h (p n)+(T+θ*h*B)/(rate*h)) at hfinal
  rw [one_div,mul_comm] at hfinal
  change (klDiv (p n) (phaseGibbs U)).toReal≤
    (1+θ)/(1-θ)*Real.exp (-rate*h*(n:ℝ))*(klDiv μ (phaseGibbs U)).toReal+
      (expectedGradientCorrection U h (p n)+(T+θ*h*B)/(rate*h))/(1-θ) at hb
  rw [div_eq_mul_inv (expectedGradientCorrection U h (p n)+(T+θ*h*B)/(rate*h))] at hb
  change (klDiv (p n) (phaseGibbs U)).toReal≤
    (17/15:ℝ)*Real.exp (-rate*h*(n:ℝ))*(klDiv μ (phaseGibbs U)).toReal+
      (16/15:ℝ)*(h^2*L/4*(∫z,U z.1∂p n)+T/(rate*h)+(4.79:ℝ)*B)
  nlinarith

end PersistencePays
#print axioms PersistencePays.A1.comparison_entropy_decay
