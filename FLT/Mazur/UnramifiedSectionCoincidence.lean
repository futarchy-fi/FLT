/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UnramifiedSectionImmersion

/-!
# Scheme-theoretic equality on the coincidence open of unramified sections

Two sections that agree at a base point agree as morphisms on an open
neighborhood. The open is the inverse image of the second section, so the
argument retains nilpotents in the original base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.UnramifiedSectionCoincidence
universe u
variable {X S : Scheme.{u}} (p : X ⟶ S)
  [FormallyUnramified p] [LocallyOfFiniteType p]
  (s t : S ⟶ X) (hs : s ≫ p = 𝟙 S) (ht : t ≫ p = 𝟙 S)

/-- The original base open where the first section lands in the second section. -/
def coincidenceOpen : S.Opens := by
  let _ := UnramifiedSectionImmersion.isOpenImmersion p t ht
  exact s ⁻¹ᵁ t.opensRange

include hs ht

/-- Membership in this open is exactly equality of the original section points. -/
theorem mem_coincidenceOpen (x : S) :
    x ∈ coincidenceOpen p s t ht ↔ s x = t x := by
  change s x ∈ Set.range t ↔ _
  constructor
  · rintro ⟨y, hy⟩
    have h : y = x := by
      have h := congrArg p hy
      change (t ≫ p) y = (s ≫ p) x at h
      rw [ht, hs] at h
      exact h
    exact (h ▸ hy).symm
  · intro h
    exact ⟨x, h.symm⟩

/-- A pointwise range factorization forces equality as scheme morphisms over the base. -/
theorem comp_eq_of_range_subset {U : Scheme.{u}} (q : U ⟶ S)
    (h : Set.range (q ≫ s) ⊆ Set.range t) : q ≫ s = q ≫ t := by
  let _ := UnramifiedSectionImmersion.isOpenImmersion p t ht
  let k := IsOpenImmersion.lift t (q ≫ s) h
  have hk : k ≫ t = q ≫ s := IsOpenImmersion.lift_fac _ _ _
  have he : k = q := by
    have he := congrArg (fun f => f ≫ p) hk
    simpa only [Category.assoc, ht, hs, Category.comp_id] using he
  exact hk.symm.trans (congrArg (fun f => f ≫ t) he)

/-- On the coincidence open the entire section morphisms agree, including on nilpotents. -/
theorem coincidenceOpen_eq :
    (coincidenceOpen p s t ht).ι ≫ s = (coincidenceOpen p s t ht).ι ≫ t := by
  apply comp_eq_of_range_subset p s t hs ht
  rintro _ ⟨x, rfl⟩
  exact x.property

/-- Every point of agreement has an affine neighborhood of actual morphism equality. -/
theorem exists_affine_eq (x : S) (hx : s x = t x) :
    ∃ U : S.Opens, IsAffineOpen U ∧ x ∈ U ∧ U.ι ≫ s = U.ι ≫ t := by
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset
    ((mem_coincidenceOpen p s t hs ht x).mpr hx)
  refine ⟨U, hU, hxU, comp_eq_of_range_subset p s t hs ht U.ι ?_⟩
  rintro _ ⟨y, rfl⟩
  exact hUV y.property

end FLT.Mazur.UnramifiedSectionCoincidence
