import PersistencePays.TransportDensity

/-! Support and absolute-continuity consequences of actual joint densities. -/
namespace PersistencePays
noncomputable section
open MeasureTheory Set
open scoped ENNReal

/-- Domination of density measures forces inclusion of their essential supports. -/
theorem density_support_of_absolutelyContinuous {S : Type*} [MeasurableSpace S]
    (base : Measure S) (r p : S → ℝ≥0∞) (hr : Measurable r) (hp : Measurable p)
    (h : base.withDensity r ≪ base.withDensity p) :
    ∀ᵐ x ∂base, p x = 0 → r x = 0 := by
  have hpos : ∀ᵐ x ∂base.withDensity p, p x ≠ 0 :=
    (ae_withDensity_iff hp).mpr (Filter.Eventually.of_forall fun _ hx => hx)
  have hh := (ae_withDensity_iff hr).mp (h.ae_le hpos)
  filter_upwards [hh] with x hx hpx
  by_contra hrx
  exact hx hrx hpx

/-- Essential support inclusion also suffices for domination of density measures. -/
theorem absolutelyContinuous_of_density_support {S : Type*} [MeasurableSpace S]
    (base : Measure S) (r p : S → ℝ≥0∞) (hr : Measurable r) (hp : Measurable p)
    (h : ∀ᵐ x ∂base, p x = 0 → r x = 0) :
    base.withDensity r ≪ base.withDensity p := by
  apply Measure.ae_le_iff_absolutelyContinuous.mp
  intro s hs
  apply (ae_withDensity_iff hr).mpr
  have hh := (ae_withDensity_iff hp).mp hs
  filter_upwards [h, hh] with x hx hsx hrx
  exact hsx (fun hpx => hrx (hx hpx))

/-- A nonnegative joint density vanishes almost everywhere above a zero marginal. -/
theorem joint_density_support_in_marginal {S T : Type*}
    [MeasurableSpace S] [MeasurableSpace T]
    (μ : Measure S) (ν : Measure T) [SFinite ν]
    (r : S × T → ℝ≥0∞) (hr : Measurable r) :
    ∀ᵐ z ∂μ.prod ν, (∫⁻ y, r (z.1, y) ∂ν) = 0 → r z = 0 := by
  have hm : Measurable (fun x => ∫⁻ y, r (x, y) ∂ν) := hr.lintegral_prod_right'
  apply (Measure.ae_prod_iff_ae_ae
    ((measurableSet_eq_fun (hm.comp measurable_fst) measurable_const).imp
      (measurableSet_eq_fun hr measurable_const))).mpr
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : (∫⁻ y, r (x, y) ∂ν) = 0
  · have hh : ∀ᵐ y ∂ν, r (x, y) = 0 :=
      (lintegral_eq_zero_iff (hr.comp (measurable_const.prodMk measurable_id))).mp hx
    filter_upwards [hh] with y hy
    exact fun _ => hy
  · exact Filter.Eventually.of_forall (fun _ h => (hx h).elim)

/-- An absolutely continuous joint law is dominated by its first marginal times volume. -/
theorem withDensity_absolutelyContinuous_fst_prod {S T : Type*}
    [MeasurableSpace S] [MeasurableSpace T]
    (μ : Measure S) (ν : Measure T) [SFinite μ] [SFinite ν]
    (r : S × T → ℝ≥0∞) (hr : Measurable r) :
    (μ.prod ν).withDensity r ≪ ((μ.prod ν).withDensity r).fst.prod ν := by
  rw [fst_withDensity_prod μ ν r hr,
    prod_withDensity_left hr.lintegral_prod_right']
  exact absolutelyContinuous_of_density_support (μ.prod ν) r _ hr
    (hr.lintegral_prod_right'.comp measurable_fst)
    (joint_density_support_in_marginal μ ν r hr)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Every transported density is conditionally dominated by any reference equivalent to volume. -/
theorem transportJoint_absolutelyContinuous_position_prod
    (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (hμ : μ ≪ (volume : Measure E).prod volume) (γ : Measure E) [SFinite γ]
    (hγ : (volume : Measure E) ≪ γ) (t : ℝ) :
    transportJoint μ t ≪ (transportPosition μ t).prod γ := by
  have hh := withDensity_absolutelyContinuous_fst_prod
    (volume : Measure E) (volume : Measure E)
    (transportedDensity μ t) (measurable_transportedDensity μ t)
  rw [← transportJoint_eq_withDensity μ hμ t] at hh
  exact hh.trans (Measure.AbsolutelyContinuous.rfl.prod hγ)

end
end PersistencePays

#print axioms PersistencePays.density_support_of_absolutelyContinuous
#print axioms PersistencePays.transportJoint_absolutelyContinuous_position_prod
