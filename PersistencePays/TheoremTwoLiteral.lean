import PersistencePays.TheoremTwoVerified

/-! Identification of the displayed finite maximum and the explicit rate
lower bound in Theorem 2, including the first-step index shift. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory

theorem finiteMaxNonnegative_attained (f:ℕ→ℝ) {n:ℕ} (hn:0<n)
    (hf:∀k<n,0≤f k) :
    ∃k, k<n ∧ finiteMaxNonnegative f n=f k ∧ ∀j<n,f j≤f k := by
  obtain ⟨k,hk,heq⟩:=Finset.exists_mem_eq_sup (Finset.range n)
    (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hn)) (fun k=>Real.toNNReal (f k))
  have hkn:k<n:=Finset.mem_range.mp hk
  have hmax:finiteMaxNonnegative f n=f k:=by
    unfold finiteMaxNonnegative
    rw [heq,Real.coe_toNNReal _ (hf k hkn)]
  exact ⟨k,hkn,hmax,fun j hj=>hmax ▸ le_finiteMaxNonnegative f hj⟩

variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem theoremTwoMomentBound_attained {U:E→ℝ} {m L:ℝ} (a:A1 U m L)
    (LH h r σ rate:ℝ) (μ:Measure (E×E)) {n:ℕ} (hn:0<n)
    (hLH:0≤LH) (hr:0≤r) (hrate:0≤rate) :
    ∃k,k<n ∧ theoremTwoMomentBound a LH h r σ rate μ n=
      LH*h^2/(12*rate)*unadjustedFlightMoment a h r σ μ k 3+
      221/(16*r)*(L*h^2)*unadjustedFlightMoment a h r σ μ k 2 ∧
      ∀j<n,LH*h^2/(12*rate)*unadjustedFlightMoment a h r σ μ j 3+
        221/(16*r)*(L*h^2)*unadjustedFlightMoment a h r σ μ j 2≤
      LH*h^2/(12*rate)*unadjustedFlightMoment a h r σ μ k 3+
        221/(16*r)*(L*h^2)*unadjustedFlightMoment a h r σ μ k 2 := by
  apply finiteMaxNonnegative_attained _ hn
  intro k hk
  have h3:0≤unadjustedFlightMoment a h r σ μ k 3:=
    integral_nonneg (fun z=>pow_nonneg (norm_nonneg _) _)
  have h2:0≤unadjustedFlightMoment a h r σ μ k 2:=
    integral_nonneg (fun z=>pow_nonneg (norm_nonneg _) _)
  positivity [a.L_pos]

theorem theorem_two_rate_lower {m h:ℝ} (hm : 0 < m) (hh : 0 ≤ h) :
    Real.sqrt m/68*Real.exp (-2*(Real.sqrt m*h))≤
      (Real.exp (-(Real.sqrt m*h)))^2*Real.sqrt m/
        (4*(16+Real.exp (-(Real.sqrt m*h)))) := by
  let r:=Real.exp (-(Real.sqrt m*h))
  have hs:0<Real.sqrt m:=Real.sqrt_pos.mpr hm
  have hr:0<r:=Real.exp_pos _
  have hr1:r≤1:=Real.exp_le_one_iff.mpr (by nlinarith)
  have he:Real.exp (-2*(Real.sqrt m*h))=r^2:=by
    dsimp [r]
    rw [←Real.exp_nat_mul]
    congr 1
    ring
  rw [he]
  change Real.sqrt m/68*r^2≤r^2*Real.sqrt m/(4*(16+r))
  apply (le_div_iff₀ (by positivity : 0<4*(16+r))).mpr
  nlinarith [mul_nonneg (show 0≤r^2*Real.sqrt m by positivity) (sub_nonneg.mpr hr1)]
theorem normalized_entropy_rate_ge {h:ℝ} (hh:0≤h) (hmax:h≤1/8) :
    (1/100:ℝ)≤(Real.exp (-h))^2/(4*(16+Real.exp (-h))) := by
  have hr:=theorem_two_rate_lower (m:=1) (h:=h) (by norm_num) hh
  norm_num only [Real.sqrt_one,one_mul,mul_one] at hr
  have he:=Real.add_one_le_exp (-2*h)
  have hnum:(3/4:ℝ)≤Real.exp (-2*h):=by linarith
  linarith

end PersistencePays
#print axioms PersistencePays.theoremTwoMomentBound_attained
#print axioms PersistencePays.theorem_two_rate_lower
