import PersistencePays.ComparisonFlightBounds

/-! Explicit normalized parameters and elementary consequences of Section 6. -/
noncomputable section
namespace PersistencePays.OBABOPath

def comparisonQ (R : ℝ) (d : ℕ) : ℝ := (1.2:ℝ)*R+27*(d:ℝ)+50

def comparisonPsi (R : ℝ) (d : ℕ) (h : ℝ) (N : ℕ) : ℝ :=
  comparisonXi R d h N + comparisonQ R d + (d:ℝ)*Real.log (1/h^2)+2*(d:ℝ)*(N:ℝ)*h

theorem comparisonQ_ge_fifty {R : ℝ} (hR : 0 ≤ R) (d : ℕ) : 50 ≤ comparisonQ R d := by
  unfold comparisonQ
  have hd := (Nat.cast_nonneg d : (0:ℝ) ≤ d)
  linarith

theorem condition_a_step_bounds {R L h : ℝ} (hR : 0 ≤ R) (hL : 1 ≤ L) (hh : 0 < h)
    (d N : ℕ)
    (ha : h^2*L*(comparisonQ R d+20*Real.log (100*((N:ℝ)+1))) ≤ 1/5000) :
    h^2*L ≤ 1/250000 ∧ h ≤ 1/500 ∧ h^2*L ≤ 1/64 := by
  have hQ := comparisonQ_ge_fifty hR d
  have hlog : 0 ≤ Real.log (100*((N:ℝ)+1)) := Real.log_nonneg (by
    have hn := (Nat.cast_nonneg N : (0:ℝ) ≤ N); nlinarith)
  have hc : 0 ≤ h^2*L := by positivity
  have hb := mul_le_mul_of_nonneg_left (show (50:ℝ) ≤ comparisonQ R d+
    20*Real.log (100*((N:ℝ)+1)) by linarith) hc
  have hs : h^2*L ≤ 1/250000 := by nlinarith
  have hl := mul_le_mul_of_nonneg_left hL (sq_nonneg h)
  exact ⟨hs, by nlinarith, by linarith⟩

theorem comparisonPsi_lower {R h : ℝ} (hR : 0 ≤ R) (hh : 0 < h) (hhmax : h ≤ 1)
    (d N : ℕ) :
    comparisonXi R d h N ≤ comparisonPsi R d h N ∧ 1 ≤ comparisonPsi R d h N := by
  have hΞ := comparisonXi_nonneg hR hh.le d N
  have hQ := comparisonQ_ge_fifty hR d
  have hlog : 0 ≤ Real.log (1/h^2) := Real.log_nonneg
    ((one_le_div (sq_pos_of_pos hh)).mpr (by nlinarith))
  have hd := (Nat.cast_nonneg d : (0:ℝ) ≤ d)
  have hn := (Nat.cast_nonneg N : (0:ℝ) ≤ N)
  unfold comparisonPsi
  constructor <;> nlinarith [mul_nonneg hd hlog, mul_nonneg hd (mul_nonneg hn hh.le)]

theorem normalized_step_logarithm {L h : ℝ} (hL : 0 < L) :
    Real.log (L/(h^2*L)) = Real.log (1/h^2) := by
  congr 1
  by_cases hh : h=0
  · simp [hh]
  · field_simp

theorem comparison_radius_scale {LH h : ℝ} (hLH : 0 < LH) (hh : 0 < h) :
    0 < (0.24:ℝ)/(LH*h^2) ∧ LH*h^3/12*((0.24:ℝ)/(LH*h^2)) = (0.02:ℝ)*h := by
  constructor
  · positivity
  · field_simp
    ring

theorem condition_b_radius_lower {LH h Q : ℝ} (hLH : 0 < LH) (hh : 0 < h)
    (N : ℕ) (hb : LH*h^2*((6.6:ℝ)*Q)^(3/2:ℝ)*(1+(N:ℝ)*h) ≤ 1/1000) :
    240*((6.6:ℝ)*Q)^(3/2:ℝ)*(1+(N:ℝ)*h) ≤ (0.24:ℝ)/(LH*h^2) := by
  apply (le_div_iff₀ (by positivity : 0 < LH*h^2)).mpr
  nlinarith

end PersistencePays.OBABOPath
#print axioms PersistencePays.OBABOPath.condition_a_step_bounds
