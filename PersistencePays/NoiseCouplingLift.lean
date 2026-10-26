import PersistencePays.MaximalCouplingKernel
import PersistencePays.FiniteNoise

/-! Disintegration lifts an endpoint coupling to a jointly measurable coupling
of its finite driving noises, with their full marginal laws preserved. -/
noncomputable section
namespace PersistencePays.NoiseCoupling
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {S B : Type*} [MeasurableSpace S] [MeasurableSpace B]
  [MeasurableSpace.CountablyGenerated S] [StandardBorelSpace B] [Nonempty B]

/-- Joint kernel of an endpoint and the independent noise used to produce it. -/
def graphKernel (μ : Measure B) (F : S×B → S) (_hF : Measurable F) : Kernel S (S×B) :=
  (Kernel.id ×ₖ Kernel.const S μ).map (fun p => (F p,p.2))

instance graphKernel_markov (μ : Measure B) [IsProbabilityMeasure μ]
    (F : S×B → S) (hF : Measurable F) : IsMarkovKernel (graphKernel μ F hF) :=
  Kernel.IsMarkovKernel.map _ (hF.prodMk measurable_snd)

theorem graphKernel_apply (μ : Measure B) [IsProbabilityMeasure μ]
    (F : S×B → S) (hF : Measurable F) (s : S) :
    graphKernel μ F hF s = μ.map (fun b => (F (s,b),b)) := by
  rw [graphKernel, Kernel.map_apply _ (hF.prodMk measurable_snd), Kernel.prod_apply,
    Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (hF.prodMk measurable_snd) (by fun_prop)]
  rfl

theorem graphKernel_fst (μ : Measure B) [IsProbabilityMeasure μ]
    (F : S×B → S) (hF : Measurable F) :
    (graphKernel μ F hF).fst = FiniteNoise.noiseKernel μ F hF := by
  ext s : 1
  rw [Kernel.fst_apply, graphKernel_apply,
    Measure.map_map measurable_fst (show Measurable (fun b : B => (F (s,b),b)) from
      (hF.comp (f:=fun b : B => (s,b)) measurable_prodMk_left).prodMk measurable_id),
    FiniteNoise.noiseKernel_apply]
  rfl

theorem graphKernel_snd (μ : Measure B) [IsProbabilityMeasure μ]
    (F : S×B → S) (hF : Measurable F) :
    (graphKernel μ F hF).snd = Kernel.const S μ := by
  ext s : 1
  rw [Kernel.snd_apply, graphKernel_apply,
    Measure.map_map measurable_snd (show Measurable (fun b : B => (F (s,b),b)) from
      (hF.comp (f:=fun b : B => (s,b)) measurable_prodMk_left).prodMk measurable_id)]
  simp [Function.comp_def]

/-- Given both endpoints, sample each driving block from its own conditional law. -/
def conditionalPair (J : Kernel S (S×B)) [IsMarkovKernel J] : Kernel ((S×S)×(S×S)) (B×B) :=
  (J.condKernel.comap (fun p => (p.1.1,p.2.1)) (by fun_prop)) ×ₖ
    (J.condKernel.comap (fun p => (p.1.2,p.2.2)) (by fun_prop))

instance conditionalPair_markov (J : Kernel S (S×B)) [IsMarkovKernel J] :
    IsMarkovKernel (conditionalPair J) := by unfold conditionalPair; infer_instance

def liftedJoint (J : Kernel S (S×B)) [IsMarkovKernel J] (C : Kernel (S×S) (S×S)) :
    Kernel (S×S) ((S×S)×(B×B)) := C ⊗ₖ conditionalPair J

instance liftedJoint_markov (J : Kernel S (S×B)) [IsMarkovKernel J]
    (C : Kernel (S×S) (S×S)) [IsMarkovKernel C] : IsMarkovKernel (liftedJoint J C) := by
  unfold liftedJoint
  infer_instance

theorem liftedJoint_left (J : Kernel S (S×B)) [IsMarkovKernel J]
    (C : Kernel (S×S) (S×S)) [IsMarkovKernel C]
    (hC : C.fst = J.fst.comap Prod.fst measurable_fst) :
    (liftedJoint J C).map (fun p => (p.1.1,p.2.1)) = J.comap Prod.fst measurable_fst := by
  ext a A hA
  rw [Kernel.map_apply' _ (by fun_prop) _ hA, liftedJoint,
    Kernel.compProd_apply ((measurable_fst.fst.prodMk measurable_snd.fst) hA)]
  have he : (fun u : S×S => conditionalPair J (a,u)
      {b : B×B | (u.1,b.1) ∈ A}) =
      (fun u : S×S => J.condKernel (a.1,u.1) (Prod.mk u.1 ⁻¹' A)) := by
    funext u
    rw [conditionalPair, Kernel.prod_apply]
    simp only [Kernel.comap_apply]
    have hset : {b : B×B | (u.1,b.1) ∈ A} = (Prod.mk u.1 ⁻¹' A) ×ˢ univ := by ext b; simp
    rw [hset, Measure.prod_prod, measure_univ, mul_one]
  change (∫⁻ u, conditionalPair J (a,u) {b : B×B | (u.1,b.1) ∈ A} ∂C a) = J a.1 A
  rw [he]
  rw [← lintegral_map (Kernel.measurable_kernel_prodMk_left' hA a.1) measurable_fst]
  change (∫⁻ u, J.condKernel (a.1,u) (Prod.mk u ⁻¹' A) ∂C.fst a) = _
  rw [hC]
  change (∫⁻ u, J.condKernel (a.1,u) (Prod.mk u ⁻¹' A) ∂J.fst a.1) = _
  rw [← Kernel.compProd_apply hA, J.disintegrate J.condKernel]

theorem liftedJoint_right (J : Kernel S (S×B)) [IsMarkovKernel J]
    (C : Kernel (S×S) (S×S)) [IsMarkovKernel C]
    (hC : C.snd = J.fst.comap Prod.snd measurable_snd) :
    (liftedJoint J C).map (fun p => (p.1.2,p.2.2)) = J.comap Prod.snd measurable_snd := by
  ext a A hA
  rw [Kernel.map_apply' _ (by fun_prop) _ hA, liftedJoint,
    Kernel.compProd_apply ((measurable_fst.snd.prodMk measurable_snd.snd) hA)]
  have he : (fun u : S×S => conditionalPair J (a,u)
      {b : B×B | (u.2,b.2) ∈ A}) =
      (fun u : S×S => J.condKernel (a.2,u.2) (Prod.mk u.2 ⁻¹' A)) := by
    funext u
    rw [conditionalPair, Kernel.prod_apply]
    simp only [Kernel.comap_apply]
    have hset : {b : B×B | (u.2,b.2) ∈ A} = univ ×ˢ (Prod.mk u.2 ⁻¹' A) := by ext b; simp
    rw [hset, Measure.prod_prod, measure_univ, one_mul]
  change (∫⁻ u, conditionalPair J (a,u) {b : B×B | (u.2,b.2) ∈ A} ∂C a) = J a.2 A
  rw [he]
  rw [← lintegral_map (Kernel.measurable_kernel_prodMk_left' hA a.2) measurable_snd]
  change (∫⁻ u, J.condKernel (a.2,u) (Prod.mk u ⁻¹' A) ∂C.snd a) = _
  rw [hC]
  change (∫⁻ u, J.condKernel (a.2,u) (Prod.mk u ⁻¹' A) ∂J.fst a.2) = _
  rw [← Kernel.compProd_apply hA, J.disintegrate J.condKernel]


def liftedNoise (J : Kernel S (S×B)) [IsMarkovKernel J] (C : Kernel (S×S) (S×S)) :
    Kernel (S×S) (B×B) := (liftedJoint J C).map Prod.snd

instance liftedNoise_markov (J : Kernel S (S×B)) [IsMarkovKernel J]
    (C : Kernel (S×S) (S×S)) [IsMarkovKernel C] : IsMarkovKernel (liftedNoise J C) :=
  Kernel.IsMarkovKernel.map _ measurable_snd

theorem liftedNoise_fst (J : Kernel S (S×B)) [IsMarkovKernel J]
    (C : Kernel (S×S) (S×S)) [IsMarkovKernel C]
    (hC : C.fst = J.fst.comap Prod.fst measurable_fst) :
    (liftedNoise J C).fst = J.snd.comap Prod.fst measurable_fst := by
  have hh := congrArg (fun H : Kernel (S×S) (S×B) => H.map Prod.snd) (liftedJoint_left J C hC)
  rw [← Kernel.map_comp_right _ (measurable_fst.fst.prodMk measurable_snd.fst) measurable_snd,
    ← Kernel.comap_map_comm J measurable_fst measurable_snd] at hh
  rw [Kernel.fst_eq, liftedNoise, ← Kernel.map_comp_right _ measurable_snd measurable_fst, Kernel.snd_eq]
  exact hh

theorem liftedNoise_snd (J : Kernel S (S×B)) [IsMarkovKernel J]
    (C : Kernel (S×S) (S×S)) [IsMarkovKernel C]
    (hC : C.snd = J.fst.comap Prod.snd measurable_snd) :
    (liftedNoise J C).snd = J.snd.comap Prod.snd measurable_snd := by
  have hh := congrArg (fun H : Kernel (S×S) (S×B) => H.map Prod.snd) (liftedJoint_right J C hC)
  rw [← Kernel.map_comp_right _ (measurable_fst.snd.prodMk measurable_snd.snd) measurable_snd,
    ← Kernel.comap_map_comm J measurable_snd measurable_snd] at hh
  rw [Kernel.snd_eq, liftedNoise, ← Kernel.map_comp_right _ measurable_snd measurable_snd, Kernel.snd_eq]
  exact hh

variable [MeasurableEq S]

theorem graphKernel_consistent (μ : Measure B) [IsProbabilityMeasure μ]
    (F : S×B → S) (hF : Measurable F) (s : S) :
    ∀ᵐ p ∂graphKernel μ F hF s, F (s,p.2) = p.1 := by
  rw [graphKernel_apply]
  rw [ae_map_iff (by exact ((hF.comp (f:=fun b : B => (s,b)) measurable_prodMk_left).prodMk
    measurable_id).aemeasurable) (by
      apply measurableSet_eq_fun
      · exact hF.comp (measurable_const.prodMk measurable_snd)
      · exact measurable_fst)]
  exact Filter.Eventually.of_forall (fun _ => rfl)

theorem liftedJoint_consistent (μ : Measure B) [IsProbabilityMeasure μ]
    (F : S×B → S) (hF : Measurable F)
    (C : Kernel (S×S) (S×S)) [IsMarkovKernel C]
    (hC1 : C.fst = (graphKernel μ F hF).fst.comap Prod.fst measurable_fst)
    (hC2 : C.snd = (graphKernel μ F hF).fst.comap Prod.snd measurable_snd)
    (a : S×S) :
    ∀ᵐ p ∂liftedJoint (graphKernel μ F hF) C a,
      F (a.1,p.2.1)=p.1.1 ∧ F (a.2,p.2.2)=p.1.2 := by
  have hleft := congrArg (fun H : Kernel (S×S) (S×B) => H a)
    (liftedJoint_left (graphKernel μ F hF) C hC1)
  have hright := congrArg (fun H : Kernel (S×S) (S×B) => H a)
    (liftedJoint_right (graphKernel μ F hF) C hC2)
  rw [Kernel.map_apply _ (by fun_prop), Kernel.comap_apply] at hleft hright
  have h1 := graphKernel_consistent μ F hF a.1
  have h2 := graphKernel_consistent μ F hF a.2
  rw [← hleft] at h1
  rw [← hright] at h2
  rw [ae_map_iff (by fun_prop) (by
    exact measurableSet_eq_fun (hF.comp (measurable_const.prodMk measurable_snd)) measurable_fst)] at h1 h2
  exact h1.and h2

/-- Disintegration preserves the entire endpoint-pair law, including exact
agreement probabilities. Neither conditional independence nor graph support is assumed. -/
theorem liftedNoise_disagreement (μ : Measure B) [IsProbabilityMeasure μ]
    (F : S×B → S) (hF : Measurable F)
    (C : Kernel (S×S) (S×S)) [IsMarkovKernel C]
    (hC1 : C.fst = (graphKernel μ F hF).fst.comap Prod.fst measurable_fst)
    (hC2 : C.snd = (graphKernel μ F hF).fst.comap Prod.snd measurable_snd)
    (a : S×S) :
    liftedNoise (graphKernel μ F hF) C a {b | F (a.1,b.1) ≠ F (a.2,b.2)} =
      C a {u | u.1 ≠ u.2} := by
  rw [liftedNoise, Kernel.map_apply' _ measurable_snd _ (by
    exact (measurableSet_eq_fun (hF.comp (measurable_const.prodMk measurable_fst))
      (hF.comp (measurable_const.prodMk measurable_snd))).compl)]
  have he : (liftedJoint (graphKernel μ F hF) C a)
      {p | F (a.1,p.2.1) ≠ F (a.2,p.2.2)} =
      (liftedJoint (graphKernel μ F hF) C a) {p | p.1.1 ≠ p.1.2} := by
    apply measure_congr
    filter_upwards [liftedJoint_consistent μ F hF C hC1 hC2 a] with p hp
    change (F (a.1,p.2.1) ≠ F (a.2,p.2.2)) = (p.1.1 ≠ p.1.2)
    rw [hp.1,hp.2]
  change (liftedJoint (graphKernel μ F hF) C a) {p | F (a.1,p.2.1) ≠ F (a.2,p.2.2)} = _
  rw [he]
  have hh := congrArg (fun H : Kernel (S×S) (S×S) => H a {u | u.1 ≠ u.2})
    (Kernel.fst_compProd C (conditionalPair (graphKernel μ F hF)))
  rw [Kernel.fst_apply' _ _ (by exact (measurableSet_eq_fun measurable_fst measurable_snd).compl)] at hh
  exact hh


end PersistencePays.NoiseCoupling
#print axioms PersistencePays.NoiseCoupling.liftedJoint_left
#print axioms PersistencePays.NoiseCoupling.liftedJoint_right

#print axioms PersistencePays.NoiseCoupling.liftedNoise_disagreement
