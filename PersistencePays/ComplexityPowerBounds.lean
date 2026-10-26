import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Exact square-root and fractional-power algebra in the gradient bound. -/
namespace PersistencePays

theorem sqrt_three_halves_eq {D:ℝ} (hD:0≤D) :
    Real.sqrt (D^(3/2:ℝ))=D^(3/4:ℝ) := by
  rw [Real.sqrt_eq_rpow,←Real.rpow_mul hD]
  norm_num

theorem sqrt_lambda_mul_lambda {Λ:ℝ} (hΛ:0≤Λ) :
    Real.sqrt Λ*Λ=Λ^(3/2:ℝ) := by
  by_cases hz:Λ=0
  · simp [hz]
  have hp:0<Λ:=lt_of_le_of_ne hΛ (Ne.symm hz)
  calc
    _ = Λ^(1/2:ℝ)*Λ^(1:ℝ):=by rw [Real.sqrt_eq_rpow,Real.rpow_one]
    _ = Λ^((1/2:ℝ)+1):=(Real.rpow_add hp _ _).symm
    _ = _:=by norm_num

theorem sqrt_mixed_complexity {L LH D:ℝ} (hL:0≤L) (hLH:0≤LH) (hD:0≤D) :
    Real.sqrt (L*D+LH*D^(3/2:ℝ))≤Real.sqrt (L*D)+Real.sqrt LH*D^(3/4:ℝ) := by
  calc
    _ ≤ Real.sqrt (L*D)+Real.sqrt (LH*D^(3/2:ℝ)):=
      by
        apply (Real.sqrt_le_left (by positivity : 0≤Real.sqrt (L*D)+Real.sqrt (LH*D^(3/2:ℝ)))).mpr
        nlinarith [Real.sq_sqrt (mul_nonneg hL hD),
          Real.sq_sqrt (mul_nonneg hLH (Real.rpow_nonneg hD (3/2:ℝ))),
          mul_nonneg (Real.sqrt_nonneg (L*D)) (Real.sqrt_nonneg (LH*D^(3/2:ℝ)))]
    _ = _ := by rw [Real.sqrt_mul hLH,sqrt_three_halves_eq hD]

theorem lambda_sqrt_mixed_complexity {L LH D Λ:ℝ}
    (hL:0≤L) (hLH:0≤LH) (hD:0≤D) (hΛ:0≤Λ) :
    Λ*Real.sqrt (Λ*(L*D+LH*D^(3/2:ℝ)))≤
      Λ^(3/2:ℝ)*(Real.sqrt (L*D)+Real.sqrt LH*D^(3/4:ℝ)) := by
  rw [Real.sqrt_mul hΛ,←mul_assoc,mul_comm Λ (Real.sqrt Λ),sqrt_lambda_mul_lambda hΛ]
  exact mul_le_mul_of_nonneg_left (sqrt_mixed_complexity hL hLH hD) (Real.rpow_nonneg hΛ _)

end PersistencePays
#print axioms PersistencePays.lambda_sqrt_mixed_complexity
