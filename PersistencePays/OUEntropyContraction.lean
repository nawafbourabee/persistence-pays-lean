import PersistencePays.GaussianShearer
import PersistencePays.GaussianChannel

/-! Exact Gaussian OU entropy contraction for arbitrary finite-entropy input
laws. The proof uses tensorization, Gaussian exchangeability, and semigroup
composition, with no smooth-density approximation. -/
open MeasureTheory ProbabilityTheory InformationTheory Real Filter
open scoped ENNReal
namespace PersistencePays
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem gaussianChannel_shearer (n : ℕ) (hn : 1 < n)
    (μ : Measure E) [IsProbabilityMeasure μ] (hD : klDiv μ (stdGaussian E) ≠ ∞) :
    (klDiv (gaussianChannel (((n : ℝ)-1)/(n : ℝ)) μ) (stdGaussian E)).toReal ≤
      (((n : ℝ)-1)/(n : ℝ))*(klDiv μ (stdGaussian E)).toReal := by
  let f : E → ℝ := fun x => (μ.rnDeriv (stdGaussian E) x).toReal
  obtain ⟨hf, hf0, hi, hl, hm, hμ⟩ := rnDeriv_entropy_data μ (stdGaussian E) hD
  let r := sqrt ((n-1 : ℕ) : ℝ) / sqrt (n : ℝ)
  let σ := (sqrt (n : ℝ))⁻¹
  let g := gaussianAverage r σ f
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have hncast : ((n-1 : ℕ) : ℝ) = (n : ℝ)-1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hq0 : 0 ≤ ((n : ℝ)-1)/(n : ℝ) :=
    div_nonneg (by rw [← hncast]; positivity) hn0.le
  have hq1 : ((n : ℝ)-1)/(n : ℝ) ≤ 1 := by apply (div_le_one hn0).2; linarith
  have hr : sqrt (((n : ℝ)-1)/(n : ℝ)) = r := by
    dsimp [r]
    rw [hncast, sqrt_div (by exact_mod_cast (show 0 ≤ (n:ℤ)-1 by omega))]
  have hs : sqrt (1-((n : ℝ)-1)/(n : ℝ)) = σ := by
    rw [show 1-((n : ℝ)-1)/(n : ℝ) = (n : ℝ)⁻¹ by field_simp; ring]
    exact sqrt_inv _
  have hnorm : r^2+σ^2=1 := by rw [← hr, ← hs]; exact gaussianChannel_normalized hq0 hq1
  have hlaw : gaussianChannel (((n : ℝ)-1)/(n : ℝ)) μ =
      (stdGaussian E).withDensity (fun x => ENNReal.ofReal (g x)) := by
    rw [gaussianChannel, hr, hs, ← hμ]
    exact gaussianUpdate_real_density r σ hnorm (by positivity) f hf hf0 hi
  letI : IsProbabilityMeasure ((stdGaussian E).withDensity (fun x => ENNReal.ofReal (g x))) :=
    hlaw ▸ gaussianChannel_probability _ μ
  have hbase := gaussianAverage_shearer n hn f hf hf0 hi hl
  have hg := entropy_density_eq_klDiv (stdGaussian E) g
    (measurable_gaussianAverage r σ f hf)
    (fun x => integral_nonneg (fun y => hf0 _))
    (integrable_gaussianAverage r σ hnorm f hi) hbase.1
  rw [← entropy_rnDeriv_eq_klDiv μ (stdGaussian E) hD, hlaw, ← hg.2]
  exact hbase.2

/-- Telescoping the adjacent ratios gives every positive rational squared
correlation, without a regularity assumption on the input law. -/
theorem gaussianChannel_natural_ratio (m n : ℕ) (hm : 0 < m) (hmn : m ≤ n)
    (μ : Measure E) [IsProbabilityMeasure μ] (hD : klDiv μ (stdGaussian E) ≠ ∞) :
    (klDiv (gaussianChannel ((m : ℝ)/(n : ℝ)) μ) (stdGaussian E)).toReal ≤
      ((m : ℝ)/(n : ℝ))*(klDiv μ (stdGaussian E)).toReal := by
  induction n generalizing m with
  | zero => omega
  | succ n ih =>
    by_cases hmeq : m=n+1
    · subst m
      rw [div_self (by positivity), gaussianChannel_one, one_mul]
    have hmn' : m ≤ n := by omega
    have hn : 0 < n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hp0 : 0 ≤ (m : ℝ)/(n : ℝ) := by positivity
    have hp1 : (m : ℝ)/(n : ℝ) ≤ 1 := (div_le_one hnR).2 (by exact_mod_cast hmn')
    have hq0 : 0 ≤ (n : ℝ)/((n+1 : ℕ) : ℝ) := by positivity
    have hq1 : (n : ℝ)/((n+1 : ℕ) : ℝ) ≤ 1 :=
      (div_le_one (by positivity)).2 (by norm_num)
    have hinner : klDiv (gaussianChannel ((m : ℝ)/(n : ℝ)) μ) (stdGaussian E) ≠ ∞ :=
      ne_top_of_le_ne_top hD (gaussianChannel_entropy_le hp0 hp1 μ)
    have hbase := gaussianChannel_shearer (n+1) (by omega)
      (gaussianChannel ((m : ℝ)/(n : ℝ)) μ) hinner
    have hcoef : ((((n+1 : ℕ) : ℝ)-1)/((n+1 : ℕ) : ℝ)) = (n : ℝ)/((n+1 : ℕ) : ℝ) := by
      push_cast
      ring
    have hprod : ((n : ℝ)/((n+1 : ℕ) : ℝ))*((m : ℝ)/(n : ℝ)) =
        (m : ℝ)/((n+1 : ℕ) : ℝ) := by field_simp
    rw [hcoef, gaussianChannel_comp hp0 hp1 hq0 hq1, hprod] at hbase
    calc
      _ ≤ ((n : ℝ)/((n+1 : ℕ) : ℝ)) *
        (klDiv (gaussianChannel ((m : ℝ)/(n : ℝ)) μ) (stdGaussian E)).toReal := hbase
      _ ≤ ((n : ℝ)/((n+1 : ℕ) : ℝ)) * (((m : ℝ)/(n : ℝ)) *
        (klDiv μ (stdGaussian E)).toReal) :=
        mul_le_mul_of_nonneg_left (ih m hm hmn') hq0
      _ = _ := by rw [← mul_assoc, hprod]

/-- The exact OU entropy contraction for every squared correlation in `[0,1]`.
Order density of the rationals and data processing replace any analytic limit
or smooth approximation argument. -/
theorem gaussianChannel_entropy_contraction_real {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (μ : Measure E) [IsProbabilityMeasure μ] (hD : klDiv μ (stdGaussian E) ≠ ∞) :
    (klDiv (gaussianChannel q μ) (stdGaussian E)).toReal ≤
      q*(klDiv μ (stdGaussian E)).toReal := by
  by_cases hqeq : q=1
  · rw [hqeq, gaussianChannel_one, one_mul]
  have hqLt : q < 1 := lt_of_le_of_ne hq1 hqeq
  have hnoninc := ENNReal.toReal_mono hD (gaussianChannel_entropy_le hq hq1 μ)
  by_cases hzero : (klDiv μ (stdGaussian E)).toReal=0
  · rw [hzero] at hnoninc ⊢
    simpa using hnoninc
  have hDpos : 0 < (klDiv μ (stdGaussian E)).toReal :=
    lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hzero)
  by_contra hbad
  have hbad' : q*(klDiv μ (stdGaussian E)).toReal <
      (klDiv (gaussianChannel q μ) (stdGaussian E)).toReal := lt_of_not_ge hbad
  have hgap : q < min 1 ((klDiv (gaussianChannel q μ) (stdGaussian E)).toReal /
      (klDiv μ (stdGaussian E)).toReal) :=
    lt_min hqLt ((lt_div_iff₀ hDpos).2 hbad')
  obtain ⟨s, hqs, hsupper⟩ := exists_rat_btwn hgap
  have hspos : (0 : ℚ) < s := by exact_mod_cast (lt_of_le_of_lt hq hqs)
  have hs1 : (s : ℝ) < 1 := lt_of_lt_of_le hsupper (min_le_left _ _)
  have hnum : 0 < s.num := Rat.num_pos.mpr hspos
  have hm : 0 < s.num.toNat := by omega
  have hn : (0 : ℝ) < s.den := by exact_mod_cast s.pos
  have hsrepr : (s : ℝ) = (s.num.toNat : ℝ)/(s.den : ℝ) := by
    rw [Rat.cast_def]
    congr 1
    exact_mod_cast (Int.toNat_of_nonneg hnum.le).symm
  have hmn : s.num.toNat ≤ s.den := by
    have hh : (s.num.toNat : ℝ) < s.den := (div_lt_one hn).1 (hsrepr ▸ hs1)
    exact_mod_cast hh.le
  have hfinite : klDiv (gaussianChannel (s : ℝ) μ) (stdGaussian E) ≠ ∞ :=
    ne_top_of_le_ne_top hD (gaussianChannel_entropy_le (by exact_mod_cast hspos.le) hs1.le μ)
  have hmono := ENNReal.toReal_mono hfinite (gaussianChannel_entropy_mono hq hqs.le hs1.le μ)
  have hrat := gaussianChannel_natural_ratio s.num.toNat s.den hm hmn μ hD
  rw [← hsrepr] at hrat
  have hsup : (s : ℝ)*(klDiv μ (stdGaussian E)).toReal <
      (klDiv (gaussianChannel q μ) (stdGaussian E)).toReal :=
    (lt_div_iff₀ hDpos).1 (lt_of_lt_of_le hsupper (min_le_right _ _))
  linarith

/-- Extended-valued form, including input laws with infinite relative entropy. -/
theorem gaussianChannel_entropy_contraction {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (μ : Measure E) [IsProbabilityMeasure μ] :
    klDiv (gaussianChannel q μ) (stdGaussian E) ≤ ENNReal.ofReal q * klDiv μ (stdGaussian E) := by
  by_cases hqzero : q=0
  · simp [hqzero, gaussianChannel_zero]
  by_cases hD : klDiv μ (stdGaussian E) = ∞
  · have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hqzero)
    simp [hD, ENNReal.ofReal_ne_zero_iff.mpr hqpos]
  have hh := ENNReal.ofReal_le_ofReal (gaussianChannel_entropy_contraction_real hq hq1 μ hD)
  have hfinite := ne_top_of_le_ne_top hD (gaussianChannel_entropy_le hq hq1 μ)
  simpa only [ENNReal.ofReal_mul hq, ENNReal.ofReal_toReal hD,
    ENNReal.ofReal_toReal hfinite] using hh

end
end PersistencePays
#print axioms PersistencePays.gaussianChannel_shearer
#print axioms PersistencePays.gaussianChannel_entropy_contraction
