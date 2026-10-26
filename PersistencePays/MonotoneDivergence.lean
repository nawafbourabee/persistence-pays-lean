import PersistencePays.CompactDifference
import PersistencePays.CutoffIntegration
import Mathlib.Analysis.InnerProductSpace.Trace

/-! The absolutely continuous derivative of a monotone field satisfies the
distributional integration-by-parts inequality. The omitted singular part has
a favorable sign. Integrability of the weighted derivative is a conclusion. -/
open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace NNReal
namespace PersistencePays.QuadraticTransport
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem compact_monotone_directional_divergence
    {T : E → E} {G : E → E →L[ℝ] E} {s : Set E}
    (hT : LocallyIntegrable T volume) (hs : volume sᶜ=0)
    (hmono : ∀ x∈s,∀ y∈s,0≤⟪T y-T x,y-x⟫)
    (hG : Measurable G)
    (hd : ∀ᵐ x ∂volume,HasFDerivWithinAt T (G x) s x)
    (hpos : ∀ᵐ x ∂volume,∀ v:E,0≤⟪v,G x v⟫)
    {w : E → ℝ} (hw : ContDiff ℝ 1 w) (hwc : HasCompactSupport w)
    (hw0 : ∀ x,0≤w x) (v : E) :
    Integrable (fun x => w x*⟪v,G x v⟫) volume ∧
    (∫ x,w x*⟪v,G x v⟫) ≤ -∫ x,(fderiv ℝ w x v)*⟪v,T x⟫ := by
  let a : ℕ → ℝ := fun n => ((n:ℝ)+1)⁻¹
  have ha : Tendsto a atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
  have ha0 : ∀ n,0<a n := fun n => by dsimp [a]; positivity
  have haR : Tendsto a atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨ha,.of_forall ha0⟩
  let f : E → ℝ := fun x => ⟪v,T x⟫
  have hf : LocallyIntegrable f volume := fun x =>
    (InnerProductSpace.toDual ℝ E v).integrableAtFilter_comp (hT x)
  let fn : ℕ → E → ℝ := fun n x => (a n)⁻¹*(f (x+a n•v)-f x)*w x
  have hfi : ∀ n,Integrable (fn n) volume := by
    intro n
    have hh := (compact_difference_integration_by_parts hw.continuous hwc hf (a n•v)).1
    simpa only [fn,mul_assoc] using hh.const_mul ((a n)⁻¹)
  have hsa : ∀ᵐ x ∂volume, x∈s ∧ ∀ n,x+a n•v∈s := by
    have hn : ∀ n,∀ᵐ x ∂volume,x+a n•v∈s := fun n =>
      (measurePreserving_add_right volume (a n•v)).quasiMeasurePreserving.ae
        (mem_ae_iff.mpr hs)
    have hh : ∀ᵐ x ∂volume,x∈s := mem_ae_iff.mpr hs
    exact hh.and (ae_all_iff.mpr hn)
  have hfn0 : ∀ n,∀ᵐ x ∂volume,0≤fn n x := by
    intro n
    filter_upwards [hsa] with x hx
    have hh := hmono x hx.1 (x+a n•v) (hx.2 n)
    rw [add_sub_cancel_left,inner_smul_right] at hh
    have hv : 0≤⟪T (x+a n•v)-T x,v⟫ :=
      nonneg_of_mul_nonneg_right hh (ha0 n)
    have hv' : 0≤f (x+a n•v)-f x := by
      dsimp [f]
      rw [← inner_sub_right,real_inner_comm]
      exact hv
    exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (ha0 n).le) hv') (hw0 x)
  have hlim : ∀ᵐ x ∂volume,Tendsto (fun n => fn n x) atTop (𝓝 (w x*⟪v,G x v⟫)) := by
    filter_upwards [hd,hsa] with x hx hxs
    have hh := directional_quotient_tendsto hx ha (fun n => (ha0 n).ne') hxs.2
    have hh' := ((tendsto_const_nhds (x:=v)).inner hh).mul_const (w x)
    simpa [fn,f,inner_smul_right,inner_sub_right,mul_comm (w x)] using hh'
  obtain ⟨C,hwl⟩ := hw.lipschitzWith_of_hasCompactSupport hwc (by simp)
  have htest := integral_compact_difference_tendsto hwl hwc (hw.differentiable one_ne_zero) hf (-v)
  have htest' : Tendsto (fun n => ∫ x,(fn n x)) atTop
      (𝓝 (-∫ x,(fderiv ℝ w x v)*f x)) := by
    have he : (fun n => ∫ x,fn n x) =
        (fun n => ∫ x,(a n)⁻¹*(w (x+a n•(-v))-w x)*f x) := by
      funext n
      simp only [fn,mul_assoc,integral_const_mul]
      rw [(compact_difference_integration_by_parts hw.continuous hwc hf (a n•v)).2]
      simp only [smul_neg,sub_eq_add_neg]
    rw [he]
    simpa only [Function.comp_def,map_neg,neg_mul,integral_neg] using htest.comp haR
  have hm : Measurable (fun x => ⟪v,G x v⟫) :=
    (InnerProductSpace.toDual ℝ E v).continuous.measurable.comp
      ((continuous_fst.clm_apply continuous_snd).measurable.comp (hG.prodMk measurable_const))
  apply nonnegative_fatou_integral_bound
    ((hw.continuous.measurable.mul hm).aestronglyMeasurable)
    (hpos.mono (fun x hx => mul_nonneg (hw0 x) (hx v))) hfi hfn0 hlim
    (fun _ => le_rfl) htest'

theorem compact_monotone_divergence
    {T : E → E} {G : E → E →L[ℝ] E} {s : Set E}
    (hT : LocallyIntegrable T volume) (hs : volume sᶜ=0)
    (hmono : ∀ x∈s,∀ y∈s,0≤⟪T y-T x,y-x⟫)
    (hG : Measurable G)
    (hd : ∀ᵐ x ∂volume,HasFDerivWithinAt T (G x) s x)
    (hpos : ∀ᵐ x ∂volume,∀ v:E,0≤⟪v,G x v⟫)
    {w : E → ℝ} (hw : ContDiff ℝ 1 w) (hwc : HasCompactSupport w)
    (hw0 : ∀ x,0≤w x) :
    Integrable (fun x => w x*(G x).toLinearMap.trace ℝ E) volume ∧
    (∫ x,w x*(G x).toLinearMap.trace ℝ E) ≤ -∫ x,(fderiv ℝ w x) (T x) := by
  classical
  let b := stdOrthonormalBasis ℝ E
  have hh := fun i => compact_monotone_directional_divergence
    hT hs hmono hG hd hpos hw hwc hw0 (b i)
  have hj : ∀ i,Integrable (fun x => (fderiv ℝ w x (b i))*⟪b i,T x⟫) volume := by
    intro i
    have hf : LocallyIntegrable (fun x => ⟪b i,T x⟫) volume := fun x =>
      (InnerProductSpace.toDual ℝ E (b i)).integrableAtFilter_comp (hT x)
    change Integrable (fun x => (fderiv ℝ w x (b i)) • ⟪b i,T x⟫) volume
    apply hf.integrable_smul_left_of_hasCompactSupport
    · exact (hw.continuous_fderiv one_ne_zero).clm_apply continuous_const
    · exact (hwc.fderiv ℝ).comp_left (g:=fun A : E →L[ℝ] ℝ => A (b i)) rfl
  have he : ∀ x,(fderiv ℝ w x) (T x) =
      ∑ i,(fderiv ℝ w x (b i))*⟪b i,T x⟫ := by
    intro x
    conv_lhs => rw [← b.sum_repr (T x)]
    rw [map_sum]
    simp only [map_smul,smul_eq_mul,b.repr_apply_apply]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hi := integrable_finsetSum (Finset.univ) (fun i _ => (hh i).1)
  have heG : (fun x => w x*(G x).toLinearMap.trace ℝ E)=
      (fun x => ∑ i,w x*⟪b i,G x (b i)⟫) := by
    funext x
    rw [LinearMap.trace_eq_sum_inner _ b,Finset.mul_sum]
    rfl
  refine ⟨by rw [heG]; exact hi,?_⟩
  rw [heG,integral_finsetSum _ (fun i _ => (hh i).1)]
  calc
    _ ≤ ∑ i, -(∫ x,(fderiv ℝ w x (b i))*⟪b i,T x⟫) :=
      Finset.sum_le_sum (fun i _ => (hh i).2)
    _ = -∫ x,(fderiv ℝ w x) (T x) := by
      rw [Finset.sum_neg_distrib,← integral_finsetSum _ (fun i _ => hj i)]
      congr 1
      apply integral_congr_ae
      filter_upwards with x
      exact (he x).symm

end
end PersistencePays.QuadraticTransport
#print axioms PersistencePays.QuadraticTransport.compact_monotone_directional_divergence
#print axioms PersistencePays.QuadraticTransport.compact_monotone_divergence
