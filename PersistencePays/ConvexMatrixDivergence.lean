import PersistencePays.LocalHessian
import PersistencePays.ConvexMollification
import PersistencePays.CompactMatrixIBP

/-! Compact matrix-valued weighted divergence for a rough convex gradient.
The positive singular Hessian is retained through mollification and Fatou;
neither a distributional Hessian theorem nor a smooth Brenier map is assumed. -/
open Set Filter MeasureTheory ContinuousLinearMap
open scoped Topology RealInnerProductSpace Convolution ContDiff
namespace PersistencePays.QuadraticTransport
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma continuous_clm_trace : Continuous (fun A : E →L[ℝ] E => A.toLinearMap.trace ℝ E) := by
  classical
  have he (A:E→L[ℝ]E) := LinearMap.trace_eq_sum_inner A.toLinearMap (stdOrthonormalBasis ℝ E)
  simp_rw [he]
  apply continuous_finsetSum
  intro i _
  exact continuous_const.inner (continuous_id.clm_apply continuous_const)

theorem compact_convex_matrix_divergence
    {φ : E → ℝ} (hφ : ConvexOn ℝ univ φ)
    {T : E → E} (he : T =ᵐ[volume] gradient φ)
    {G : E → E →L[ℝ] E} {s : Set E}
    (hs : volume sᶜ=0) (hG : Measurable G)
    (hd : ∀ᵐ x ∂volume,HasFDerivWithinAt T (G x) s x)
    (hpos : ∀ᵐ x ∂volume,(G x).toLinearMap.IsPositive)
    {S : E → E →L[ℝ] E} (hS : ContDiff ℝ 1 S)
    (hSc : HasCompactSupport S) (hSp : ∀ x,(S x).toLinearMap.IsPositive) :
    Integrable (fun x => ((S x).comp (G x)).toLinearMap.trace ℝ E) volume ∧
    (∫ x,((S x).comp (G x)).toLinearMap.trace ℝ E) ≤
      -∫ x,⟪matrixDivergence S x,T x⟫ := by
  have hTi := (convex_gradient_locallyIntegrable hφ).congr he.symm
  have hGi := convex_hessian_locallyIntegrable hφ he hs hG hd hpos
  let r : Set E := {x | x∈s ∧ DifferentiableAt ℝ φ x ∧ T x=gradient φ x}
  have hr : volume rᶜ=0 := by
    apply mem_ae_iff.mp
    filter_upwards [mem_ae_iff.mpr hs,convexOn_ae_differentiable volume hφ,he]
      with x hx hdx hex
    exact ⟨hx,(hdx (mem_univ x)).2,hex⟩
  have hmono : ∀ x∈r,∀ y∈r,0≤⟪T y-T x,y-x⟫ := by
    intro x hx y hy
    rw [hx.2.2,hy.2.2]
    exact supports_monotone (convex_gradient_supports hφ hy.2.1)
      (convex_gradient_supports hφ hx.2.1)
  have hdr := hd.mono (fun x hx => hx.mono (fun y (hy:y∈r) => hy.1))
  have hpos0 := hpos.mono (fun _ hx => hx.re_inner_nonneg_right)
  let Gn : ℕ → E → E →L[ℝ] E := fun n => smoothKernel n ⋆[lsmul ℝ ℝ,volume] G
  have hGn : ∀ n,Continuous (Gn n) := fun n =>
    ((smoothKernel_compact n).contDiff_convolution_left (lsmul ℝ ℝ)
      (smoothKernel_contDiff n) hGi).continuous
  have hGn0 : ∀ n x v,0≤⟪v,Gn n x v⟫ := by
    intro n x v
    rw [convolution_quadratic (smoothKernel_contDiff n).continuous (smoothKernel_compact n) hGi]
    apply integral_nonneg_of_ae
    filter_upwards [hpos0] with y hy
    exact mul_nonneg (smoothKernel_nonneg n (x-y)) (hy v)
  have hdom : ∀ n x v,⟪v,Gn n x v⟫≤⟪v,fderiv ℝ (mollify n T) x v⟫ := by
    intro n x v
    exact mollified_derivative_dominates hTi hGi hr hmono hG hdr hpos0
      ((smoothKernel_contDiff n).of_le (by norm_num))
      (smoothKernel_compact n) (smoothKernel_nonneg n) x v
  let fn : ℕ → E → ℝ := fun n x => ((S x).comp (Gn n x)).toLinearMap.trace ℝ E
  have hfi : ∀ n,Integrable (fn n) volume := by
    intro n
    have hc : Continuous (fn n) := continuous_clm_trace.comp (hS.continuous.clm_comp (hGn n))
    apply hc.integrable_of_hasCompactSupport
    apply hSc.mono'
    intro x hx
    contrapose! hx
    simp only [Function.mem_support,not_not]
    simp [fn,image_eq_zero_of_notMem_tsupport hx]
  have hfn0 : ∀ n,∀ᵐ x ∂volume,0≤fn n x := fun n => .of_forall (fun x =>
    positive_trace_comp_nonneg (S x).toLinearMap (Gn n x).toLinearMap (hSp x) (hGn0 n x))
  have hlimitG : ∀ᵐ x ∂volume,Tendsto (fun n => Gn n x) atTop (𝓝 (G x)) :=
    ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      shrinkingBump_rOut_tendsto (Eventually.of_forall (fun _ => le_rfl)) hGi
  have hlimit : ∀ᵐ x ∂volume,Tendsto (fun n => fn n x) atTop
      (𝓝 (((S x).comp (G x)).toLinearMap.trace ℝ E)) := by
    filter_upwards [hlimitG] with x hx
    exact continuous_clm_trace.continuousAt.tendsto.comp
      ((continuous_fst.clm_comp continuous_snd).continuousAt.tendsto.comp
        ((tendsto_const_nhds (x:=S x)).prodMk_nhds hx))
  have hbound : ∀ n,(∫ x,fn n x)≤-∫ x,⟪matrixDivergence S x,mollify n T x⟫ := by
    intro n
    have hi := compact_matrix_ibp hS hSc ((mollify_contDiff hTi n).of_le (by norm_num))
      (fun x => (hSp x).isSymmetric)
    apply (integral_mono_ae (hfi n) hi.1 _).trans_eq hi.2.2
    filter_upwards with x
    exact positive_trace_comp_mono (S x).toLinearMap (Gn n x).toLinearMap
      (fderiv ℝ (mollify n T) x).toLinearMap (hSp x) (hdom n x)
  have hm : Measurable (fun x => ((S x).comp (G x)).toLinearMap.trace ℝ E) :=
    continuous_clm_trace.measurable.comp
      ((continuous_fst.clm_comp continuous_snd).measurable.comp (hS.continuous.measurable.prodMk hG))
  exact nonnegative_fatou_integral_bound hm.aestronglyMeasurable
    (hpos0.mono (fun x hx => positive_trace_comp_nonneg (S x).toLinearMap
      (G x).toLinearMap (hSp x) hx)) hfi hfn0 hlimit hbound
    (compact_pairing_mollify_tendsto hφ he
      (matrixDivergence_continuous hS) (matrixDivergence_compact hSc)).neg

end
end PersistencePays.QuadraticTransport
#print axioms PersistencePays.QuadraticTransport.compact_convex_matrix_divergence
