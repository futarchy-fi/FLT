/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UnramifiedSectionCoincidence

/-!
# Simultaneous local matching of finite unramified section families

A finite marking match at one base point extends to actual morphism equalities
on a single affine neighborhood, over an arbitrary possibly nonreduced base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.UnramifiedFiniteSectionMatching
open UnramifiedSectionCoincidence
universe u v
variable {X S : Scheme.{u}} (p : X ⟶ S)
  [FormallyUnramified p] [LocallyOfFiniteType p]
  {L : Type v} [Finite L] (s t : L → (S ⟶ X))
  (hs : ∀ a, s a ≫ p = 𝟙 S) (ht : ∀ a, t a ≫ p = 𝟙 S)

/-- The simultaneous matching open retains all of the original section maps. -/
def matchingOpen : S.Opens := ⨅ a, coincidenceOpen p (s a) (t a) (ht a)

include hs ht

/-- Its points are exactly the simultaneous matches of the original finite families. -/
theorem mem_matchingOpen (x : S) :
    x ∈ matchingOpen p s t ht ↔ ∀ a, s a x = t a x := by
  simp only [matchingOpen, ← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
  exact forall_congr' (fun a => mem_coincidenceOpen p (s a) (t a) (hs a) (ht a) x)

/-- On any smaller base open, all matching sections agree as scheme morphisms. -/
theorem eq_on_open {U : S.Opens} (hU : U ≤ matchingOpen p s t ht) (a : L) :
    U.ι ≫ s a = U.ι ≫ t a := by
  apply comp_eq_of_range_subset p (s a) (t a) (hs a) (ht a)
  rintro _ ⟨y, rfl⟩
  exact ⟨y.val, ((mem_matchingOpen p s t hs ht y.val).mp (hU y.property) a).symm⟩

/-- A finite pointwise match extends to one affine neighborhood of exact section equalities. -/
theorem exists_affine_matching (x : S) (hx : ∀ a, s a x = t a x) :
    ∃ U : S.Opens, IsAffineOpen U ∧ x ∈ U ∧ ∀ a, U.ι ≫ s a = U.ι ≫ t a := by
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset
    ((mem_matchingOpen p s t hs ht x).mpr hx)
  exact ⟨U, hU, hxU, eq_on_open p s t hs ht hUV⟩

/-- Pointwise relabeling gives actual locally constant relabeling on affine neighborhoods. -/
theorem exists_affine_relabel {G : Type*} (r : G → L → L) (x : S)
    (hx : ∃ g, ∀ a, s (r g a) x = t a x) :
    ∃ (g : G) (U : S.Opens), IsAffineOpen U ∧ x ∈ U ∧
      ∀ a, U.ι ≫ s (r g a) = U.ι ≫ t a := by
  obtain ⟨g, hg⟩ := hx
  obtain ⟨U, hU, hxU, he⟩ := exists_affine_matching p (fun a => s (r g a)) t
    (fun a => hs (r g a)) ht x hg
  exact ⟨g, U, hU, hxU, he⟩

end FLT.Mazur.UnramifiedFiniteSectionMatching
