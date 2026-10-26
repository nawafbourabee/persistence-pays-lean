import PersistencePays.EntropyRecurrence

/-! The scalar combination of entropy and transport-corrector dissipation.
These lemmas do not assume that an unspecified functional is the actual
corrector; that identification remains an analytic obligation in Section 4. -/

namespace PersistencePays

theorem corrector_young_bound {X V C θ δ : ℝ}
    (hX : 0 ≤ X) (hV : 0 ≤ V) (hθ : 0 ≤ θ) (hδ : 0 ≤ δ)
    (hC : |C| ≤ 2*Real.sqrt (V*X)) :
    -θ*δ*C ≤ δ/2*V+2*θ^2*δ*X := by
  have hsV := Real.sq_sqrt hV
  have hsX := Real.sq_sqrt hX
  have hs := sq_nonneg (Real.sqrt V-2*θ*Real.sqrt X)
  have hy : 2*θ*Real.sqrt (V*X) ≤ V/2+2*θ^2*X := by
    rw [Real.sqrt_mul hV]
    nlinarith
  have hc := neg_abs_le C
  have hcb : -C ≤ 2*Real.sqrt (V*X) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hcb (mul_nonneg hθ hδ)
  have hymul := mul_le_mul_of_nonneg_left hy hδ
  nlinarith

/-- The exact scalar one-step inequality used in Proposition 4.12, after
normalizing the corrector by sqrt(m). The three coefficient conditions are
kept explicit, to be checked from the actual OU parameters. -/
theorem entropy_corrector_one_step
    {X V W EntNext C CNext θ δ r h a1 a2 b defect : ℝ}
    (hX : 0 ≤ X) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hθ : 0 ≤ θ) (hδ : 0 ≤ δ) (hr : 0 ≤ r) (hh : 0 ≤ h) (ha2 : 0 ≤ a2)
    (hrsq : r^2 = 1-δ)
    (hC : |C| ≤ 2*Real.sqrt (V*X))
    (hH : X+V+θ*C ≤ (1+θ)*(X+V))
    (hEntStep : EntNext ≤ X+V-δ*(V+W)+defect)
    (hCStep : CNext ≤ r^2*C+h*a1*(V+W)-r*h*a2*X+h*b)
    (hc1 : θ*h*a1 ≤ δ/4)
    (hc2 : 2*θ*δ ≤ r*h*a2/2)
    (hc3 : θ*r*h*a2/2 ≤ δ/4) :
    EntNext+θ*CNext ≤
      (1-θ*r*a2*h/(2*(1+θ)))*(X+V+θ*C)+defect+θ*h*b := by
  have hy := corrector_young_bound hX hV hθ hδ hC
  have hc := mul_le_mul_of_nonneg_left hCStep hθ
  rw [hrsq] at hc
  have hcv := mul_le_mul_of_nonneg_right hc1 hV
  have hcw := mul_le_mul_of_nonneg_right hc1 hW
  have hcx := mul_le_mul_of_nonneg_right hc2 (mul_nonneg hθ hX)
  have hdec := mul_le_mul_of_nonneg_right hc3 hV
  have hdW := mul_nonneg hδ hW
  have hcoarse : EntNext+θ*CNext ≤ X+V+θ*C-
      (θ*r*h*a2/2)*(X+V)+defect+θ*h*b := by
    nlinarith
  have hd : 0 < 1+θ := by linarith
  have hq : 0 ≤ θ*r*h*a2/2 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hH (div_nonneg hq hd.le)
  have he : (θ*r*h*a2/2/(1+θ))*((1+θ)*(X+V)) =
      (θ*r*h*a2/2)*(X+V) := by field_simp <;> ring
  rw [he] at hscaled
  have hrate : θ*r*h*a2/2/(1+θ) = θ*r*a2*h/(2*(1+θ)) := by
    field_simp <;> ring
  rw [hrate] at hscaled
  nlinarith

end PersistencePays

#print axioms PersistencePays.corrector_young_bound
#print axioms PersistencePays.entropy_corrector_one_step
