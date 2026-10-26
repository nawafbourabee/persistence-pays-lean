import PersistencePays.FlowDensityCharacteristic
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Constructions.Polish.Basic

noncomputable section
namespace PersistencePays
open MeasureTheory Set
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A differentiable bijection satisfying the pointwise density-Jacobian identity transports
exactly the corresponding Lebesgue densities. No law-transport assertion is an assumption. -/
theorem density_pushforward_of_jacobian (μ:Measure E) [μ.IsAddHaarMeasure]
    {f:E→E} {J:E→E→L[ℝ]E} (hf:∀x,HasFDerivAt f (J x) x)
    (hbij:Function.Bijective f) {n0 n1:E→ℝ} (hn0:Measurable n0) (hn1:Measurable n1)
    (hpos:∀x,0≤n1 x)
    (hid:∀x,n1 (f x)*|(J x).det|=n0 x) :
    (μ.withDensity (fun x=>ENNReal.ofReal (n0 x))).map f=
      μ.withDensity (fun x=>ENNReal.ofReal (n1 x)) := by
  have hfm:Measurable f := (continuous_iff_continuousAt.mpr
    (fun x=>(hf x).continuousAt)).measurable
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg hfm,
    lintegral_withDensity_eq_lintegral_mul _ hn0.ennreal_ofReal
      (show Measurable (fun x=>g (f x)) from hg.comp hfm),
    lintegral_withDensity_eq_lintegral_mul _ hn1.ennreal_ofReal hg]
  have hc := lintegral_image_eq_lintegral_abs_det_fderiv_mul μ MeasurableSet.univ
    (fun x (_:x∈(univ:Set E))=>(hf x).hasFDerivWithinAt)
    hbij.1.injOn (fun x=>ENNReal.ofReal (n1 x)*g x)
  rw [Set.image_univ,Set.range_eq_univ.mpr hbij.2,Measure.restrict_univ] at hc
  change (∫⁻x,ENNReal.ofReal (n0 x)*g (f x) ∂μ)=
    ∫⁻x,ENNReal.ofReal (n1 x)*g x ∂μ
  rw [hc]
  apply lintegral_congr
  intro x
  change ENNReal.ofReal (n0 x)*g (f x)=_
  rw [←hid x,ENNReal.ofReal_mul (hpos (f x))]
  ac_rfl

/-- The actual characteristic flow of the continuity equation transports its density. -/
theorem VariationalFlow.transports_density (μ:Measure E) [μ.IsAddHaarMeasure]
    {m:ℝ→E→E} {Dm:ℝ→E→E→L[ℝ]E} {a b:ℝ}
    (flow:VariationalFlow E m Dm a b) (hab:a≤b)
    (n:ℝ×E→ℝ) (hn:∀t∈Icc a b,∀x,DifferentiableAt ℝ n (t,x))
    (hpos:∀t∈Icc a b,∀x,0<n (t,x))
    (hpde:∀t∈Icc a b,∀x,
      fderiv ℝ n (t,x) (1,m t x)=
        -n (t,x)*LinearMap.trace ℝ E (Dm t x).toLinearMap)
    {t:ℝ} (ht:t∈Icc a b) :
    (μ.withDensity (fun x=>ENNReal.ofReal (n (a,x)))).map (flow.toFun t)=
      μ.withDensity (fun x=>ENNReal.ofReal (n (t,x))) := by
  have hm (u:ℝ) (hu:u∈Icc a b) : Measurable (fun x=>n (u,x)) := by
    apply Continuous.measurable
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (hn u hu x).continuousAt.comp (continuous_const.prodMk continuous_id).continuousAt
  apply density_pushforward_of_jacobian μ (flow.spatial_derivative t ht)
    (flow.bijective t ht) (hm a ⟨le_rfl,hab⟩) (hm t ht)
    (fun x=>(hpos t ht x).le)
  intro x
  rw [abs_of_pos (flow.jacobian_det_pos hab n hn hpos hpde ht x)]
  exact flow.density_jacobian hab n hn hpde ht x

/-- The same transport identity backwards, for any measurable inverse of the flow. -/
theorem VariationalFlow.transports_density_inverse (μ:Measure E) [μ.IsAddHaarMeasure]
    {m:ℝ→E→E} {Dm:ℝ→E→E→L[ℝ]E} {a b:ℝ}
    (flow:VariationalFlow E m Dm a b) (hab:a≤b)
    (n:ℝ×E→ℝ) (hn:∀t∈Icc a b,∀x,DifferentiableAt ℝ n (t,x))
    (hpos:∀t∈Icc a b,∀x,0<n (t,x))
    (hpde:∀t∈Icc a b,∀x,
      fderiv ℝ n (t,x) (1,m t x)=
        -n (t,x)*LinearMap.trace ℝ E (Dm t x).toLinearMap)
    {t:ℝ} (ht:t∈Icc a b) {g:E→E} (hg:Measurable g)
    (hinv:Function.LeftInverse g (flow.toFun t)) :
    (μ.withDensity (fun x=>ENNReal.ofReal (n (t,x)))).map g=
      μ.withDensity (fun x=>ENNReal.ofReal (n (a,x))) := by
  rw [←flow.transports_density μ hab n hn hpos hpde ht,
    Measure.map_map hg (continuous_iff_continuousAt.mpr
      (fun x=>(flow.spatial_derivative t ht x).continuousAt)).measurable]
  have heq : g ∘ flow.toFun t=id := funext hinv
  rw [heq,Measure.map_id]

/-- A classical finite-dimensional flow has an actual measurable two-sided inverse. -/
theorem VariationalFlow.exists_measurable_inverse
    {m:ℝ→E→E} {Dm:ℝ→E→E→L[ℝ]E} {a b:ℝ}
    (flow:VariationalFlow E m Dm a b) {t:ℝ} (ht:t∈Icc a b) :
    ∃g:E→E,Measurable g ∧ Function.LeftInverse g (flow.toFun t) ∧
      Function.RightInverse g (flow.toFun t) := by
  have hc : Continuous (flow.toFun t) := continuous_iff_continuousAt.mpr
    (fun x=>(flow.spatial_derivative t ht x).continuousAt)
  have he := hc.measurableEmbedding (flow.bijective t ht).1
  refine ⟨he.invFun,he.measurable_invFun,he.leftInverse_invFun,?_⟩
  intro y
  obtain ⟨x,rfl⟩ := (flow.bijective t ht).2 y
  rw [he.leftInverse_invFun x]

end PersistencePays
#print axioms PersistencePays.density_pushforward_of_jacobian
#print axioms PersistencePays.VariationalFlow.transports_density

#print axioms PersistencePays.VariationalFlow.transports_density_inverse
#print axioms PersistencePays.VariationalFlow.exists_measurable_inverse
