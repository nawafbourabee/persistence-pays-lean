import PersistencePays.GaussianTarget
import PersistencePays.GaussianTilt

/-! Exact connection of actual diagonal Verlet to the scalar Appendix B factors. -/
namespace PersistencePays
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
variable {ι : Type*} [Fintype ι]

theorem diagonal_verlet_position (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (h : ℝ) (z : ι → ℝ × ℝ) (i : ι) :
    Real.sqrt (a i) *
      ((verlet (gradient (diagonalPotential a)) h (diagonalPhaseMap a z)).1 i) =
        scalarVerletPosition (h*Real.sqrt (a i)) (z i) := by
  rw [diagonalPotential_gradient]
  simp only [verlet, kick, drift, diagonalPhaseMap, diagonalLinear, PiLp.add_apply,
    PiLp.sub_apply, PiLp.smul_apply, WithLp.toLp_ofLp, WithLp.ofLp_toLp, smul_eq_mul,
    scalarVerletPosition, tiltA]
  change Real.sqrt (a i) * ((z i).1/Real.sqrt (a i) +
    h*((z i).2-h/2*(a i*((z i).1/Real.sqrt (a i))))) = _
  have hs2 := Real.sq_sqrt (ha i).le
  have hsne := (Real.sqrt_pos.2 (ha i)).ne'
  generalize hv : Real.sqrt (a i) = s at *
  rw [← hs2]
  field_simp
  ring

theorem diagonal_trapezoidDefect (a : ι → ℝ) (x y : EuclideanSpace ℝ ι) :
    trapezoidDefect (diagonalPotential a) (gradient (diagonalPotential a)) x y = 0 := by
  rw [diagonalPotential_quadratic]
  exact lemma_2_1_quadratic (diagonalLinear a).toContinuousLinearMap 0 0
    (diagonalLinear_symmetric a) x y

theorem diagonal_gradient_norm_sq (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (x : EuclideanSpace ℝ ι) :
    ‖gradient (diagonalPotential a) x‖^2 = ∑ i, a i*(Real.sqrt (a i)*x i)^2 := by
  rw [diagonalPotential_gradient, EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  rw [diagonalLinear_apply, mul_pow, mul_pow, Real.sq_sqrt (ha i).le]
  ring

/-- The literal Verlet energy increment is exactly the sum of the scalar work defects. -/
theorem diagonal_verlet_energyDefect (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (h : ℝ) (z : ι → ℝ × ℝ) :
    phaseEnergy (diagonalPotential a)
        (verlet (gradient (diagonalPotential a)) h (diagonalPhaseMap a z)) -
      phaseEnergy (diagonalPotential a) (diagonalPhaseMap a z) =
        ∑ i, scalarVerletWork (h*Real.sqrt (a i)) (z i) := by
  rw [phaseEnergy_eq_norm, phaseEnergy_eq_norm, verlet_energy_identity_norm,
    diagonal_trapezoidDefect, add_zero, diagonal_gradient_norm_sq a ha,
    diagonal_gradient_norm_sq a ha, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [diagonal_verlet_position a ha]
  have hx : Real.sqrt (a i)*(diagonalPhaseMap a z).1 i = (z i).1 := by
    change Real.sqrt (a i)*((z i).1/Real.sqrt (a i)) = _
    field_simp [(Real.sqrt_pos.2 (ha i)).ne']
  rw [hx]
  unfold scalarVerletWork
  rw [mul_pow, Real.sq_sqrt (ha i).le]
  ring

end
end PersistencePays

#print axioms PersistencePays.diagonal_verlet_energyDefect
