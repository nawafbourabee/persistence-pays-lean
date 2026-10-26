import PersistencePays.ConditionalCovariance
import PersistencePays.ConvexMatrixDivergence

/-! The matrix field in Appendix A is identified with the covariance of the
actual conditional law through its bilinear form, not an independent proxy. -/
open Set Filter MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped Topology RealInnerProductSpace
namespace PersistencePays
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem covariance_field_positive (μ:Measure E) (S:E→L[ℝ]E) {n:ℝ} (hn:0≤n)
    (hS:∀ u v:E,⟪u,S v⟫=n*covarianceBilin μ u v) : S.toLinearMap.IsPositive := by
  refine ⟨?_,?_⟩
  · intro u v
    change ⟪S u,v⟫=⟪u,S v⟫
    rw [real_inner_comm,hS,hS,covarianceBilin_comm (μ:=μ) v u]
  · intro v
    change 0≤⟪S v,v⟫
    rw [real_inner_comm,hS]
    exact mul_nonneg hn (covarianceBilin_self_nonneg v)

theorem continuous_positive_of_ae {S:E→E→L[ℝ]E} (hS:Continuous S)
    (hp:∀ᵐ x ∂volume,(S x).toLinearMap.IsPositive) :
    ∀ x,(S x).toLinearMap.IsPositive := by
  intro x
  refine ⟨?_,?_⟩
  · intro u v
    have he : (fun y => ⟪S y u,v⟫) =ᵐ[volume] (fun y => ⟪u,S y v⟫) :=
      hp.mono (fun y hy => hy.isSymmetric u v)
    exact congrFun (Measure.eq_of_ae_eq he
      ((hS.clm_apply continuous_const).inner continuous_const)
      (continuous_const.inner (hS.clm_apply continuous_const))) x
  · intro v
    change 0≤⟪S x v,v⟫
    have hd : Dense {y | 0≤⟪S y v,v⟫} :=
      Measure.dense_of_ae (hp.mono (fun y hy => hy.re_inner_nonneg_left v))
    have hc : IsClosed {y | 0≤⟪S y v,v⟫} :=
      isClosed_le continuous_const ((hS.clm_apply continuous_const).inner continuous_const)
    have heq : {y | 0≤⟪S y v,v⟫} = univ := hc.closure_eq.symm.trans hd.closure_eq
    have hx : x ∈ {y | 0≤⟪S y v,v⟫} := by rw [heq]; trivial
    exact hx

theorem covariance_field_trace (μ:Measure E) [IsProbabilityMeasure μ]
    (hm:MemLp id 2 μ) (S K:E→L[ℝ]E) {n:ℝ}
    (hS:∀ u v:E,⟪u,S v⟫=n*covarianceBilin μ u v)
    (hK:K.toLinearMap.IsSymmetric) :
    (S.comp K).toLinearMap.trace ℝ E = n*covarianceContraction μ K.toLinearMap := by
  classical
  let b := stdOrthonormalBasis ℝ E
  let a := ∫ y,y ∂μ
  have hi (i:Fin (Module.finrank ℝ E)) :
      Integrable (fun z => ⟪b i,z-a⟫*⟪K (b i),z-a⟫) μ := by
    have h1 := (inner_memLp_two μ hm (b i)).sub (memLp_const ⟪b i,a⟫)
    have h2 := (inner_memLp_two μ hm (K (b i))).sub (memLp_const ⟪K (b i),a⟫)
    have hh := h1.integrable_mul h2
    change Integrable (fun z => (⟪b i,z⟫-⟪b i,a⟫)*(⟪K (b i),z⟫-⟪K (b i),a⟫)) μ at hh
    simpa only [inner_sub_right] using hh
  have he (z:E) : (∑ i,⟪b i,z⟫*⟪K (b i),z⟫)=⟪z,K z⟫ := by
    have hs (i:Fin (Module.finrank ℝ E)) : ⟪K (b i),z⟫=⟪b i,K z⟫ := hK _ _
    rw [← b.sum_inner_mul_inner z (K z)]
    apply Finset.sum_congr rfl
    intro i _
    rw [hs,real_inner_comm (b i) z]
  rw [LinearMap.trace_eq_sum_inner _ b]
  have heS (i:Fin (Module.finrank ℝ E)) : ⟪b i,(S.comp K) (b i)⟫=
      n*(∫ z,⟪b i,z-a⟫*⟪K (b i),z-a⟫ ∂μ) := by
    rw [comp_apply,hS,covarianceBilin_apply hm]
    rfl
  change (∑ i,⟪b i,(S.comp K) (b i)⟫)=_
  simp_rw [heS]
  rw [← Finset.mul_sum,← integral_finsetSum _ (fun i _ => hi i)]
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  exact he (z-a)

end
end PersistencePays
#print axioms PersistencePays.covariance_field_trace
#print axioms PersistencePays.continuous_positive_of_ae
