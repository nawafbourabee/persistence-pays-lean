import PersistencePays.GaussianHalfMass
import PersistencePays.GaussianTargetVerlet
import PersistencePays.StationaryFlow
import PersistencePays.GibbsRegularity

/-! Proposition 2.4: the actual scheduled adjusted OBABO chain on the diagonal Gaussian. -/
noncomputable section
namespace PersistencePays.GaussianLowerBound
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- One soft eigenvalue and `k` stiff eigenvalues; the dimension is `k+1`. -/
def twoScaleSpectrum (k : ℕ) (m L : ℝ) : Fin (k+1) → ℝ := Fin.cases m (fun _ => L)

theorem twoScaleSpectrum_pos (k : ℕ) (m L : ℝ) (hm : 0 < m) (hL : 0 < L) :
    ∀ i, 0 < twoScaleSpectrum k m L i := by
  intro i
  exact Fin.cases hm (fun _ => hL) i

def twoScalePotential (k : ℕ) (m L : ℝ) : EuclideanSpace ℝ (Fin (k+1)) → ℝ :=
  diagonalPotential (twoScaleSpectrum k m L)

theorem twoScalePotential_A1 (k : ℕ) (m L : ℝ) (hm : 0 < m) (hmL : m ≤ L) :
    A1 (twoScalePotential k m L) m L := by
  apply diagonalPotential_A1 _ _ _ hm hmL
  · intro i; exact Fin.cases le_rfl (fun _ => hmL) i
  · intro i; exact Fin.cases hmL (fun _ => le_rfl) i

theorem twoScalePotential_A2 (k : ℕ) (m L : ℝ) : A2 (twoScalePotential k m L) 0 :=
  diagonalPotential_A2 _

@[fun_prop] theorem twoScalePotential_measurable (k : ℕ) (m L : ℝ) :
    Measurable (twoScalePotential k m L) := by
  unfold twoScalePotential diagonalPotential
  fun_prop

@[fun_prop] theorem twoScaleGradient_measurable (k : ℕ) (m L : ℝ) :
    Measurable (gradient (twoScalePotential k m L)) := by
  unfold twoScalePotential
  rw [diagonalPotential_gradient]
  exact (diagonalLinear _).toContinuousLinearMap.continuous.measurable

theorem twoScale_frequency (k : ℕ) (m L h : ℝ) (i : Fin (k+1)) :
    h * Real.sqrt (twoScaleSpectrum k m L i) =
      coordinateFrequency k (h * Real.sqrt m) (h * Real.sqrt L) i := by
  refine Fin.cases ?_ (fun _ => ?_) i <;> rfl

theorem twoScale_crossing_preimage (k : ℕ) (m L : ℝ) (hm : 0 < m) (hL : 0 < L) (h : ℝ) :
    diagonalPhaseMap (twoScaleSpectrum k m L) ⁻¹'
      proposalCrossing (gradient (twoScalePotential k m L)) h (softHalfspace k) =
      coordinateCrossing k (h*Real.sqrt m) := by
  ext z
  change ((z 0).1/Real.sqrt m ≤ 0 ∧
    ¬ (verlet (gradient (twoScalePotential k m L)) h
      (diagonalPhaseMap (twoScaleSpectrum k m L) z)).1 0 ≤ 0) ↔ _
  rw [not_le]
  have hp := diagonal_verlet_position (twoScaleSpectrum k m L)
    (twoScaleSpectrum_pos k m L hm hL) h z 0
  change Real.sqrt m * _ = scalarVerletPosition (h*Real.sqrt m) (z 0) at hp
  change _ ↔ ((z 0).1 ≤ 0 ∧ 0 < scalarVerletPosition (h*Real.sqrt m) (z 0))
  rw [← hp]
  have hs := Real.sqrt_pos.mpr hm
  constructor
  · rintro ⟨ha,hb⟩
    exact ⟨(div_le_iff₀ hs).mp ha |> (by simpa using ·), mul_pos hs hb⟩
  · rintro ⟨ha,hb⟩
    exact ⟨(div_le_iff₀ hs).mpr (by simpa using ha), (mul_pos_iff_of_pos_left hs).mp hb⟩

theorem twoScale_accepted_crossing_bound (k : ℕ) (m L h : ℝ)
    (hm : 0 < m) (hL : 0 < L) (hh : 0 < h) :
    (∫⁻ w, (proposalCrossing (gradient (twoScalePotential k m L)) h (softHalfspace k)).indicator
      (fun w => ENNReal.ofReal (min 1 (Real.exp
        (-energyIncrement (phaseEnergy (twoScalePotential k m L))
          (verlet (gradient (twoScalePotential k m L)) h) w)))) w
       ∂phaseGibbs (twoScalePotential k m L)) ≤
      ENNReal.ofReal (h*Real.sqrt m / (2 * Real.sqrt 2) * gaussianRho (h*Real.sqrt L)^k) := by
  rw [show phaseGibbs (twoScalePotential k m L) = _ from
    diagonal_phaseGibbs (twoScaleSpectrum k m L) (twoScaleSpectrum_pos k m L hm hL)]
  rw [lintegral_map (by
    apply Measurable.indicator
    · unfold energyIncrement phaseEnergy
      fun_prop
    · exact proposalCrossing_measurable _ (twoScaleGradient_measurable k m L) _ _
        (softHalfspace_measurable k)) (by fun_prop)]
  have he : (fun z : Fin (k+1) → ℝ×ℝ =>
      (proposalCrossing (gradient (twoScalePotential k m L)) h (softHalfspace k)).indicator
        (fun w => ENNReal.ofReal (min 1 (Real.exp
          (-energyIncrement (phaseEnergy (twoScalePotential k m L))
            (verlet (gradient (twoScalePotential k m L)) h) w))))
        (diagonalPhaseMap (twoScaleSpectrum k m L) z)) =
      (fun z => (coordinateCrossing k (h*Real.sqrt m)).indicator
        (fun z => ENNReal.ofReal (min 1 (Real.exp
          (-coordinateWork k (h*Real.sqrt m) (h*Real.sqrt L) z)))) z) := by
    funext z
    have hc := Set.ext_iff.mp (twoScale_crossing_preimage k m L hm hL h) z
    simp only [Set.mem_preimage] at hc
    have hw := diagonal_verlet_energyDefect (twoScaleSpectrum k m L)
      (twoScaleSpectrum_pos k m L hm hL) h z
    simp_rw [twoScale_frequency] at hw
    change energyIncrement (phaseEnergy (twoScalePotential k m L))
      (verlet (gradient (twoScalePotential k m L)) h)
      (diagonalPhaseMap (twoScaleSpectrum k m L) z) =
        coordinateWork k (h*Real.sqrt m) (h*Real.sqrt L) z at hw
    by_cases hz : z ∈ coordinateCrossing k (h*Real.sqrt m)
    · rw [indicator_of_mem (hc.mpr hz), indicator_of_mem hz, hw]
    · rw [indicator_of_notMem (fun hz' => hz (hc.mp hz')), indicator_of_notMem hz]
  rw [he]
  exact product_accepted_crossing_bound k _ _ (mul_pos hh (Real.sqrt_pos.mpr hm))
    (mul_pos hh (Real.sqrt_pos.mpr hL))

/-- Actual law after `n` attempted steps, from the two-warm halfspace start,
with any deterministic threshold-refresh schedule. -/
def gaussianAttemptLaw (k : ℕ) (m L h r σ : ℝ) (refresh : ℕ → Bool) (n : ℕ) :=
  evolve (fun j => scheduledStepKernel (twoScalePotential k m L)
    (twoScalePotential_measurable k m L) (gradient (twoScalePotential k m L))
    (twoScaleGradient_measurable k m L) h r σ (refresh j))
      ((2 : ℝ≥0∞) • (extendedTarget (twoScalePotential k m L)).restrict
        (positionCylinder (softHalfspace k))) n

/-- Exact step-dependent Gaussian lower bound for every threshold schedule,
including an independent threshold every step and one threshold per epoch. -/
theorem proposition_2_4_step_bound (k : ℕ) (m L h r σ : ℝ)
    (hm : 0 < m) (hmL : m ≤ L) (hh : 0 < h) (hnorm : r^2+σ^2=1)
    (refresh : ℕ → Bool) (n : ℕ)
    (hn : (n:ℝ) * (h*Real.sqrt m / Real.sqrt 2 * gaussianRho (h*Real.sqrt L)^k) < 1/4) :
    (1/4 : ℝ≥0∞) < probabilityTV
      ((gaussianAttemptLaw k m L h r σ refresh n).map (fun z => z.1.1))
      (positionGibbs (twoScalePotential k m L)) := by
  apply scheduled_half_conditioned_TV_gt_quarter (twoScalePotential k m L)
    (twoScalePotential_measurable k m L) (twoScalePotential_A1 k m L hm hmL).gibbs_integrable
    (gradient (twoScalePotential k m L)) (twoScaleGradient_measurable k m L)
    h r σ hnorm refresh (softHalfspace k) (softHalfspace_measurable k)
    (diagonal_half_mass k _ (twoScaleSpectrum_pos k m L hm (hm.trans_le hmL)))
    (ENNReal.ofReal (h*Real.sqrt m/(2*Real.sqrt 2)*gaussianRho (h*Real.sqrt L)^k))
    (twoScale_accepted_crossing_bound k m L h hm (hm.trans_le hmL) hh) n
  have he : (n : ℝ≥0∞)*2*
      ENNReal.ofReal (h*Real.sqrt m/(2*Real.sqrt 2)*gaussianRho (h*Real.sqrt L)^k) =
    ENNReal.ofReal ((n:ℝ)*(h*Real.sqrt m/Real.sqrt 2*gaussianRho (h*Real.sqrt L)^k)) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  rw [he]
  simpa using (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0:ℝ)<1/4)).mpr hn


/-- The scalar optimization retains the exact square-root condition number. -/
theorem gaussian_crossing_dimension_bound (k : ℕ) (hk : 1 ≤ k) (m L h : ℝ)
    (hm : 0 < m) (hL : 0 < L) (hh : 0 < h) :
    h*Real.sqrt m/Real.sqrt 2*gaussianRho (h*Real.sqrt L)^k ≤
      Real.sqrt 2 / (Real.sqrt (L/m) * ((k+1:ℕ):ℝ)^(1/6:ℝ)) := by
  have hs2 : 0 < Real.sqrt (2:ℝ) := by positivity
  have hsm := Real.sqrt_pos.mpr hm
  have hsL := Real.sqrt_pos.mpr hL
  have hd : (0:ℝ) < (k+1:ℕ) := by positivity
  have hdp : 0 < ((k+1:ℕ):ℝ)^(1/6:ℝ) := Real.rpow_pos_of_pos hd _
  have hb := gaussian_step_acceptance_optimization (k+1) (by omega)
    (h*Real.sqrt L) (mul_pos hh hsL)
  simp only [Nat.add_sub_cancel] at hb
  calc
    _ = (Real.sqrt m/(Real.sqrt 2*Real.sqrt L)) *
        (h*Real.sqrt L*gaussianRho (h*Real.sqrt L)^k) := by field_simp
    _ ≤ (Real.sqrt m/(Real.sqrt 2*Real.sqrt L)) * (2/((k+1:ℕ):ℝ)^(1/6:ℝ)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by
      rw [Real.sqrt_div hL.le]
      field_simp
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

/-- Proposition 2.4, optimized over every positive step size. The dimension is
`k+1`; this is an actual position-TV lower bound for the adjusted chain. -/
theorem proposition_2_4 (k : ℕ) (hk : 1 ≤ k) (m L h r σ : ℝ)
    (hm : 0 < m) (hmL : m ≤ L) (hh : 0 < h) (hnorm : r^2+σ^2=1)
    (refresh : ℕ → Bool) (n : ℕ)
    (hn : (n:ℝ) < Real.sqrt 2/8 * Real.sqrt (L/m) * ((k+1:ℕ):ℝ)^(1/6:ℝ)) :
    (1/4 : ℝ≥0∞) < probabilityTV
      ((gaussianAttemptLaw k m L h r σ refresh n).map (fun z => z.1.1))
      (positionGibbs (twoScalePotential k m L)) := by
  apply proposition_2_4_step_bound k m L h r σ hm hmL hh hnorm refresh n
  have hL := hm.trans_le hmL
  have hκ : 0 < Real.sqrt (L/m) := Real.sqrt_pos.mpr (div_pos hL hm)
  have hd : (0:ℝ) < (k+1:ℕ) := by positivity
  have hdp : 0 < ((k+1:ℕ):ℝ)^(1/6:ℝ) := Real.rpow_pos_of_pos hd _
  calc
    _ ≤ (n:ℝ)*(Real.sqrt 2/(Real.sqrt (L/m)*((k+1:ℕ):ℝ)^(1/6:ℝ))) :=
      mul_le_mul_of_nonneg_left (gaussian_crossing_dimension_bound k hk m L h hm hL hh)
        (Nat.cast_nonneg n)
    _ < (Real.sqrt 2/8*Real.sqrt (L/m)*((k+1:ℕ):ℝ)^(1/6:ℝ)) *
        (Real.sqrt 2/(Real.sqrt (L/m)*((k+1:ℕ):ℝ)^(1/6:ℝ))) :=
      mul_lt_mul_of_pos_right hn (by positivity)
    _ = 1/4 := by
      field_simp
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

/-- The sharper step-dependent form preceding the optimization in Appendix B. -/
theorem proposition_2_4_explicit_step (k : ℕ) (m L h r σ : ℝ)
    (hm : 0 < m) (hmL : m ≤ L) (hh : 0 < h) (hnorm : r^2+σ^2=1)
    (refresh : ℕ → Bool) (n : ℕ)
    (hn : (n:ℝ) < Real.sqrt (2*(L/m))/(4*(h*Real.sqrt L)) *
      (Real.sqrt (1+(h*Real.sqrt L)^6/64))^k) :
    (1/4 : ℝ≥0∞) < probabilityTV
      ((gaussianAttemptLaw k m L h r σ refresh n).map (fun z => z.1.1))
      (positionGibbs (twoScalePotential k m L)) := by
  apply proposition_2_4_step_bound k m L h r σ hm hmL hh hnorm refresh n
  have hL := hm.trans_le hmL
  have hsm := Real.sqrt_pos.mpr hm
  have hsL := Real.sqrt_pos.mpr hL
  have hs2 : 0 < Real.sqrt (2:ℝ) := by positivity
  have hd : 0 < Real.sqrt (1+(h*Real.sqrt L)^6/64) := by positivity
  have hc : 0 < h*Real.sqrt m/Real.sqrt 2*gaussianRho (h*Real.sqrt L)^k := by
    exact mul_pos (div_pos (mul_pos hh hsm) hs2) (pow_pos (gaussianRho_pos _) _)
  have hh' := mul_lt_mul_of_pos_right hn hc
  calc
    _ < (Real.sqrt (2*(L/m))/(4*(h*Real.sqrt L)) *
      (Real.sqrt (1+(h*Real.sqrt L)^6/64))^k) *
        (h*Real.sqrt m/Real.sqrt 2*gaussianRho (h*Real.sqrt L)^k) := hh'
    _ = 1/4 := by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_div hL.le]
      unfold gaussianRho
      rw [inv_pow]
      field_simp


end PersistencePays.GaussianLowerBound
#print axioms PersistencePays.GaussianLowerBound.proposition_2_4_step_bound

#print axioms PersistencePays.GaussianLowerBound.proposition_2_4
#print axioms PersistencePays.GaussianLowerBound.proposition_2_4_explicit_step
