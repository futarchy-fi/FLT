/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSplitNodePointSeparation
public import FLT.Mazur.PolygonOneGonNodePointSeparation
public import FLT.Mazur.PolygonCubicClosedImmersionCriterion

/-!
# Global point separation and the cubic closed immersion

Linear coordinate charts detect individual torus components and exclude all
nodes. Node-value coordinate charts distinguish the split nodes; the one-gon
has a single node. Local torus injectivity therefore gives global injectivity.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonCubicSections
open PolygonPinching ProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ)

include h in
/-- Every point is on a torus or is a specified node. -/
lemma point_torus_or_node (v : C.left) :
    (∃ i x, (torusToComponent K ≫ componentι K n i ≫ p).left x = v) ∨
      ∃ i z, (nodeι K n i ≫ q).left z = v := by
  let := polygon_lfp K n hn p q h
  by_cases hv : v ∈ C.hom.smoothLocus
  · left
    change v ∈ (C.hom.smoothLocus : Set C.left) at hv
    rw [smooth_range K n hn p q h] at hv
    exact Set.mem_iUnion.mp hv
  · exact Or.inr ((PolygonNodeLocus.nonsmooth_iff K n hn p q h v).mp hv)

/-- All node images avoid every branch-linear coordinate chart. -/
lemma node_image_not_mem_linear (i j : Fin n) (z : Spec (.of K)) :
    cubicProjectiveMorphism K n hn p q h a ((nodeι K n i ≫ q).left z) ∉
      chart K _ (interpolationIndex n j 1) := by
  rcases n with _ | (_ | m)
  · exact (Nat.not_lt_zero _ hn).elim
  · exact PolygonOneGonCubicCoordinates.node_image_not_mem_linear K hn p q h a i z j
  · exact PolygonSplitCubicCoordinates.node_image_not_mem_linear
      K (m + 2) hn p q h a (by omega) i z j

/-- The full inverse image of a linear-coordinate chart is exactly its torus open. -/
lemma cubicProjectiveMorphism_preimage_linear (i : Fin n) :
    cubicProjectiveMorphism K n hn p q h a ⁻¹ᵁ chart K _ (interpolationIndex n i 1) =
      torusOpen K n hn p q h i := by
  apply le_antisymm
  · intro v hv
    rcases point_torus_or_node K n hn p q h v with ⟨j, x, rfl⟩ | ⟨j, x, rfl⟩
    · have hji := (torus_image_mem_linear_iff K n hn p q h a j i x).mp hv
      subst j
      exact ⟨x, rfl⟩
    · exact (node_image_not_mem_linear K n hn p q h a j i x hv).elim
  · rintro v ⟨x, rfl⟩
    exact (torus_image_mem_linear_iff K n hn p q h a i i x).mpr rfl

/-- Two node images can coincide only when their node indices coincide. -/
lemma node_image_eq_index (i j : Fin n) (x y : Spec (.of K))
    (he : cubicProjectiveMorphism K n hn p q h a ((nodeι K n i ≫ q).left x) =
      cubicProjectiveMorphism K n hn p q h a ((nodeι K n j ≫ q).left y)) : i = j := by
  by_cases hn₂ : 2 ≤ n
  · have hi := (PolygonSplitCubicCoordinates.node_image_mem_node_iff
      K n hn p q h a hn₂ i x i).mpr rfl
    rw [he] at hi
    exact ((PolygonSplitCubicCoordinates.node_image_mem_node_iff
      K n hn p q h a hn₂ j y i).mp hi).symm
  · have : n = 1 := by omega
    subst n
    exact Subsingleton.elim _ _

/-- The actual cubic map separates every pair of scheme points. -/
theorem cubicProjectiveMorphism_injective :
    Function.Injective (cubicProjectiveMorphism K n hn p q h a) := by
  intro v w he
  rcases point_torus_or_node K n hn p q h v with ⟨i, x, rfl⟩ | ⟨i, x, rfl⟩ <;>
    rcases point_torus_or_node K n hn p q h w with ⟨j, y, rfl⟩ | ⟨j, y, rfl⟩
  · have hi := (torus_image_mem_linear_iff K n hn p q h a i i x).mpr rfl
    rw [he] at hi
    have hij := (torus_image_mem_linear_iff K n hn p q h a j i y).mp hi
    subst j
    let := torus_isImmersion K n hn p q h a i
    let v : (torusOpen K n hn p q h i).toScheme :=
      ⟨(torusToComponent K ≫ componentι K n i ≫ p).left x, ⟨x, rfl⟩⟩
    let w : (torusOpen K n hn p q h i).toScheme :=
      ⟨(torusToComponent K ≫ componentι K n i ≫ p).left y, ⟨y, rfl⟩⟩
    exact congrArg (fun z ↦ (torusOpen K n hn p q h i).ι z)
      (((torusOpen K n hn p q h i).ι ≫ cubicProjectiveMorphism K n hn p q h a).isEmbedding.injective
         (show ((torusOpen K n hn p q h i).ι ≫ cubicProjectiveMorphism K n hn p q h a) v =
          ((torusOpen K n hn p q h i).ι ≫ cubicProjectiveMorphism K n hn p q h a) w from he))
  · have hi := (torus_image_mem_linear_iff K n hn p q h a i i x).mpr rfl
    rw [he] at hi
    exact (node_image_not_mem_linear K n hn p q h a j i y hi).elim
  · have hj := (torus_image_mem_linear_iff K n hn p q h a j j y).mpr rfl
    rw [← he] at hj
    exact (node_image_not_mem_linear K n hn p q h a i j x hj).elim
  · have hij := node_image_eq_index K n hn p q h a i j x y he
    subst j
    have hxy : (x : Spec (.of K)) = y := Subsingleton.elim (α := Spec (.of K)) x y
    exact congrArg (nodeι K n i ≫ q).left hxy

/-- The cubic morphism is a global closed immersion for every nonempty polygon. -/
theorem cubicProjectiveMorphism_isClosedImmersion :
    IsClosedImmersion (cubicProjectiveMorphism K n hn p q h a) :=
  (cubicProjectiveMorphism_isClosedImmersion_iff_injective K n hn p q h a).mpr
    (cubicProjectiveMorphism_injective K n hn p q h a)

end FLT.Mazur.PolygonCubicSections
