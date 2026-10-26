import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.List.Forall2

/-! Rockafellar's convex potential for a cyclically monotone relation.
The domain records where the real supremum is finite; no finite-potential or
subgradient conclusion is assumed. -/
open Set
open scoped RealInnerProductSpace
namespace PersistencePays
namespace QuadraticTransport
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def pathWeight (a : E × E) : List (E × E) → E → ℝ
  | [], x => ⟪a.2, x-a.1⟫
  | b::l, x => ⟪a.2, b.1-a.1⟫ + pathWeight b l x

/-- Every finite closed chain of points in the relation has nonpositive
displacement work. This is the usual cyclic-monotonicity inequality. -/
def CyclicallyMonotone (Γ : Set (E × E)) : Prop :=
  ∀ a ∈ Γ, ∀ l : List (E × E), (∀ z ∈ l, z ∈ Γ) → pathWeight a l a.1 ≤ 0

structure RelationPath (Γ : Set (E × E)) where
  nodes : List (E × E)
  mem : ∀ z ∈ nodes, z ∈ Γ

instance (Γ : Set (E × E)) : Nonempty (RelationPath Γ) :=
  ⟨⟨[], by simp⟩⟩

def potentialDomain (Γ : Set (E × E)) (a : E × E) : Set E :=
  {x | BddAbove (range (fun p : RelationPath Γ => pathWeight a p.nodes x))}

def rockafellarPotential (Γ : Set (E × E)) (a : E × E) (x : E) : ℝ :=
  sSup (range (fun p : RelationPath Γ => pathWeight a p.nodes x))

lemma pathWeight_append (a z : E × E) (l : List (E × E)) (x : E) :
    pathWeight a (l ++ [z]) x = pathWeight a l z.1 + ⟪z.2, x-z.1⟫ := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih => simp only [List.cons_append, pathWeight, ih]; ring

lemma pathWeight_affine (a : E × E) (l : List (E × E)) (x y : E)
    (u v : ℝ) (huv : u+v=1) :
    pathWeight a l (u • x+v • y) = u*pathWeight a l x+v*pathWeight a l y := by
  induction l generalizing a with
  | nil =>
    simp only [pathWeight, inner_sub_right, inner_add_right, inner_smul_right]
    nlinarith [congrArg (fun r : ℝ => r * ⟪a.2, a.1⟫) huv]
  | cons b l ih =>
    simp only [pathWeight, ih]
    nlinarith [congrArg (fun r : ℝ => r * ⟪a.2, b.1-a.1⟫) huv]

lemma pathWeight_le_potential {Γ : Set (E × E)} {a : E × E} {x : E}
    (hx : x ∈ potentialDomain Γ a) (p : RelationPath Γ) :
    pathWeight a p.nodes x ≤ rockafellarPotential Γ a x :=
  le_csSup hx (mem_range_self p)

theorem potentialDomain_convex (Γ : Set (E × E)) (a : E × E) :
    Convex ℝ (potentialDomain Γ a) := by
  intro x hx y hy u v hu hv huv
  obtain ⟨bx, hbx⟩ := hx
  obtain ⟨by', hby⟩ := hy
  refine ⟨u*bx+v*by', ?_⟩
  rintro _ ⟨p, rfl⟩
  dsimp only
  rw [pathWeight_affine a p.nodes x y u v huv]
  exact add_le_add (mul_le_mul_of_nonneg_left (hbx (mem_range_self p)) hu)
    (mul_le_mul_of_nonneg_left (hby (mem_range_self p)) hv)

theorem rockafellarPotential_convex (Γ : Set (E × E)) (a : E × E) :
    ConvexOn ℝ (potentialDomain Γ a) (rockafellarPotential Γ a) := by
  refine ⟨potentialDomain_convex Γ a, ?_⟩
  intro x hx y hy u v hu hv huv
  apply csSup_le (range_nonempty _)
  rintro _ ⟨p, rfl⟩
  dsimp only
  rw [pathWeight_affine a p.nodes x y u v huv]
  exact add_le_add (mul_le_mul_of_nonneg_left (pathWeight_le_potential hx p) hu)
    (mul_le_mul_of_nonneg_left (pathWeight_le_potential hy p) hv)

theorem relation_in_potentialDomain {Γ : Set (E × E)} (hΓ : CyclicallyMonotone Γ)
    {a z : E × E} (ha : a ∈ Γ) (hz : z ∈ Γ) : z.1 ∈ potentialDomain Γ a := by
  refine ⟨⟪z.2, z.1-a.1⟫, ?_⟩
  rintro _ ⟨p, rfl⟩
  have hh := hΓ a ha (p.nodes ++ [z]) (by
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact p.mem b hb
    · simpa using (List.mem_singleton.mp hb ▸ hz))
  rw [pathWeight_append] at hh
  have hneg : ⟪z.2, a.1-z.1⟫ = -⟪z.2, z.1-a.1⟫ := by
    rw [← inner_neg_right, neg_sub]
  rw [hneg] at hh
  linarith

/-- Every pair of the original cyclically monotone relation lies in the
subgradient of the constructed convex function on its effective domain. -/
theorem rockafellar_subgradient {Γ : Set (E × E)} (hΓ : CyclicallyMonotone Γ)
    {a z : E × E} (ha : a ∈ Γ) (hz : z ∈ Γ) {x : E}
    (hx : x ∈ potentialDomain Γ a) :
    rockafellarPotential Γ a z.1 + ⟪z.2, x-z.1⟫ ≤ rockafellarPotential Γ a x := by
  have hzdom := relation_in_potentialDomain hΓ ha hz
  have hh : rockafellarPotential Γ a z.1 ≤ rockafellarPotential Γ a x - ⟪z.2, x-z.1⟫ := by
    apply csSup_le (range_nonempty _)
    rintro _ ⟨p, rfl⟩
    let p' : RelationPath Γ := ⟨p.nodes ++ [z], by
      intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact p.mem b hb
      · simpa using (List.mem_singleton.mp hb ▸ hz)⟩
    have hp := pathWeight_le_potential hx p'
    change pathWeight a (p.nodes ++ [z]) x ≤ _ at hp
    rw [pathWeight_append] at hp
    linarith
  linarith

end
end QuadraticTransport
end PersistencePays
#print axioms PersistencePays.QuadraticTransport.rockafellar_subgradient
