import PersistencePays.EntropyDissipationAlgebra
import PersistencePays.OUScalarBounds

/-! Exact numerical parameter checks for Theorem 2 in normalized units m=1. -/

namespace PersistencePays

theorem theorem_two_normalized_parameters (h : ℝ) (hh : 0 < h) (hhmax : h ≤ 3/16) :
    let r := Real.exp (-h)
    let θ := r/16
    let δ := 1-r^2
    let rate := r^2/(4*(16+r))
    0 < θ ∧ θ ≤ 1/16 ∧
      θ*h*(13/2:ℝ) ≤ δ/4 ∧
      2*θ*δ ≤ r*h*(1/2:ℝ)/2 ∧
      θ*r*h*(1/2:ℝ)/2 ≤ δ/4 ∧
      θ*r*(1/2:ℝ)/(2*(1+θ)) = rate ∧
      r^2/68 ≤ rate ∧ 0 < rate*h ∧ rate*h ≤ 1 ∧
      (1+θ)/(1-θ) ≤ 17/15 ∧ 1/(1-θ) ≤ 16/15 ∧
      (θ/rate)*(13/4:ℝ) ≤ 221/(16*r) := by
  dsimp only
  let r := Real.exp (-h)
  obtain ⟨hr, hr1, _, hnorm, _, hdlo, _, hsup⟩ := normalized_ou_coefficients h hh.le
  have hr0 : 0 < r := hr
  have hrmax : r ≤ 1 := hr1
  have hrsq : r^2 ≤ 1 := by nlinarith
  have hd0 : 0 ≤ 1-r^2 := by linarith
  have hdhigh : 1-r^2 ≤ 2*h := by
    change (Real.exp (-h))^2 + (Real.sqrt (1-Real.exp (-2*h)))^2 = 1 at hnorm
    dsimp [r]
    nlinarith
  have hd : 0 < 4*(16+r) := by positivity
  have hden : 0 < 1-r/16 := by linarith
  have hratepos : 0 < r^2/(4*(16+r)) := div_pos (sq_pos_of_pos hr0) hd
  have hrateupper : r^2/(4*(16+r)) ≤ 1/64 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith
  change 0 < r/16 ∧ r/16 ≤ 1/16 ∧ _
  refine ⟨by positivity, by linarith, ?_, ?_, ?_, ?_, ?_,
    mul_pos hratepos hh, ?_, ?_, ?_, ?_⟩
  · have hhprod := mul_le_mul_of_nonneg_right hrmax hh.le
    change 2*h*(1-h) ≤ 1-r^2 at hdlo
    nlinarith
  · have hp := mul_le_mul_of_nonneg_left hdhigh hr0.le
    nlinarith
  · change 2*h*(1-h) ≤ 1-r^2 at hdlo
    have hp := mul_le_mul_of_nonneg_right hrsq hh.le
    nlinarith
  · field_simp
    <;> ring
  · apply (le_div_iff₀ hd).mpr
    have hp := mul_le_mul_of_nonneg_left hrmax (sq_nonneg r)
    nlinarith
  · have hp := mul_le_mul_of_nonneg_right hrateupper hh.le
    nlinarith
  · apply (div_le_iff₀ hden).mpr
    linarith
  · apply (div_le_iff₀ hden).mpr
    linarith
  · have he : (r/16/(r^2/(4*(16+r))))*(13/4:ℝ) = 13*(16+r)/(16*r) := by
      field_simp
      <;> ring
    rw [he]
    apply (div_le_div_iff_of_pos_right (by positivity : 0 < 16*r)).mpr
    linarith

end PersistencePays

#print axioms PersistencePays.theorem_two_normalized_parameters
