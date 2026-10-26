import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Uniform logarithmic bounds used in the implementable Theorem 1 schedule. -/
noncomputable section
namespace PersistencePays

def theoremOneLogScale (L LH D:ℝ):ℝ := Real.log (2+L+LH+D)

theorem theoremOne_log_bounds {L LH D:ℝ} (hL:1≤L) (hLH:0≤LH) (hD:1≤D) :
    1≤theoremOneLogScale L LH D ∧
    L≤Real.exp (theoremOneLogScale L LH D) ∧
    D≤Real.exp (theoremOneLogScale L LH D) ∧
    LH≤Real.exp (theoremOneLogScale L LH D) ∧
    Real.log D≤theoremOneLogScale L LH D ∧
    Real.log L≤theoremOneLogScale L LH D ∧
    Real.log (1+LH)≤theoremOneLogScale L LH D := by
  have hK:0<2+L+LH+D:=by linarith
  have he:Real.exp (theoremOneLogScale L LH D)=2+L+LH+D:=Real.exp_log hK
  have h1:1≤theoremOneLogScale L LH D:=by
    apply Real.exp_le_exp.mp
    rw [he]
    linarith [Real.exp_one_lt_three]
  refine ⟨h1,?_,?_,?_,?_,?_,?_⟩
  · rw [he];linarith
  · rw [he];linarith
  · rw [he];linarith
  · exact Real.log_le_log (by linarith) (by linarith)
  · exact Real.log_le_log (by linarith) (by linarith)
  · exact Real.log_le_log (by linarith) (by linarith)

theorem theoremOne_logScale_pos {L LH D:ℝ} (hL:1≤L) (hLH:0≤LH) (hD:1≤D) :
    0<theoremOneLogScale L LH D := by
  have hh:=(theoremOne_log_bounds hL hLH hD).1
  linarith

theorem theoremOne_logScale_le_sum {L LH D:ℝ} (hL:1≤L) (hLH:0≤LH) (hD:1≤D) :
    theoremOneLogScale L LH D≤2+L+LH+D := by
  exact (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)

theorem theoremOne_log_logScale_le {L LH D:ℝ} (hL:1≤L) (hLH:0≤LH) (hD:1≤D) :
    Real.log (theoremOneLogScale L LH D)≤theoremOneLogScale L LH D := by
  exact (Real.log_le_sub_one_of_pos (theoremOne_logScale_pos hL hLH hD)).trans (by linarith)

/-- Products and arbitrary nonnegative powers have only logarithmic cost in
all scale parameters. Constants remain explicit. -/
theorem log_product_powers_le {a b c p q r C Λ:ℝ}
    (ha:0<a) (hb:0<b) (hc:0<c) (hC:0<C)
    (hp:0≤p) (hq:0≤q) (hr:0≤r)
    (haL:Real.log a≤Λ) (hbL:Real.log b≤Λ) (hcL:Real.log c≤Λ) :
    Real.log (C*a^p*b^q*c^r)≤Real.log C+(p+q+r)*Λ := by
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul hC.ne' (by positivity),
    Real.log_rpow ha,Real.log_rpow hb,Real.log_rpow hc]
  nlinarith [mul_le_mul_of_nonneg_left haL hp,mul_le_mul_of_nonneg_left hbL hq,
    mul_le_mul_of_nonneg_left hcL hr]

end PersistencePays
#print axioms PersistencePays.theoremOne_log_bounds
#print axioms PersistencePays.log_product_powers_le
