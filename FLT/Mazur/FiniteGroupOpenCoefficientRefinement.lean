/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupOpenRelationCoefficients

/-!
# Compatibility of original open coefficients under source refinement

The coefficient attached to an original invariant open section restricts
exactly to the coefficient on a smaller stable source chart. Refining twice
gives the same invariant ring map as the direct inclusion.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FiniteGroupOpenRelation
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {G : Type} [Group G] {X : Scheme} (ρ : G →* Aut X)
  (U : X.Opens) (hU : ∀ g : G, (ρ g).hom ⁻¹ᵁ U = U)
  (U' : X.Opens) (hU' : ∀ g : G, (ρ g).hom ⁻¹ᵁ U' = U') (h : U' ≤ U)

/-- The actual restriction map between invariant coordinates of nested stable charts. -/
def invariantRestriction : invariantCoordinates (restrictedAction ρ U hU) →+*
    invariantCoordinates (restrictedAction ρ U' hU') :=
  invariantMap (restrictedAction ρ U' hU') (restrictedAction ρ U hU) (X.homOfLE h)
    (fun g ↦ (inclusion_equivariant ρ U hU U' hU' h g).symm)

/-- Invariant restriction retains the exact scheme function restriction. -/
theorem invariantRestriction_val (a : invariantCoordinates (restrictedAction ρ U hU)) :
    (invariantRestriction ρ U hU U' hU' h a).val = (X.homOfLE h).appTop a.val := rfl

/-- Two successive source refinements equal the direct restriction on every invariant function. -/
theorem invariantRestriction_trans (U'' : X.Opens)
    (hU'' : ∀ g : G, (ρ g).hom ⁻¹ᵁ U'' = U'') (h' : U'' ≤ U')
    (a : invariantCoordinates (restrictedAction ρ U hU)) :
    invariantRestriction ρ U' hU' U'' hU'' h' (invariantRestriction ρ U hU U' hU' h a) =
      invariantRestriction ρ U hU U'' hU'' (h'.trans h) a := by
  apply Subtype.ext
  simp only [invariantRestriction_val]
  change (((X.homOfLE h).appTop ≫ (X.homOfLE h').appTop) a.val) = _
  rw [← Scheme.Hom.comp_appTop, Scheme.homOfLE_homOfLE]

variable {B C : Scheme} (b : X ⟶ B) (r s : C ⟶ B) (z : G → (X ⟶ C))
  (hr : ∀ g, z g ≫ r = b) (hs : ∀ g, z g ≫ s = (ρ g).hom ≫ b)
  (V : B.Opens) (hV : r ⁻¹ᵁ V = s ⁻¹ᵁ V)
  (hUV : U ≤ b ⁻¹ᵁ V) (hU'V : U' ≤ b ⁻¹ᵁ V)
  (t : Γ(V.toScheme, ⊤))
  (ht : (r ∣_ V).appTop t = (s.resLE V _ hV.le).appTop t)

/-- Refinement preserves the exact endpoint map into the original coefficient domain. -/
theorem openEndpoint_refinement :
    X.homOfLE h ≫ openEndpoint b V U hUV = openEndpoint b V U' hU'V := by
  apply (cancel_mono V.ι).mp
  simp only [openEndpoint, Category.assoc, Scheme.Hom.resLE_comp_ι,
    Scheme.homOfLE_ι_assoc]

/-- The coefficient of the same original open section agrees on every source refinement. -/
theorem invariantCoefficient_refinement :
    invariantRestriction ρ U hU U' hU' h
        (invariantCoefficient ρ b r s z hr hs V hV U hU hUV t ht) =
      invariantCoefficient ρ b r s z hr hs V hV U' hU' hU'V t ht := by
  apply Subtype.ext
  simp only [invariantRestriction_val, invariantCoefficient_val]
  change (((openEndpoint b V U hUV).appTop ≫ (X.homOfLE h).appTop) t) = _
  rw [← Scheme.Hom.comp_appTop, openEndpoint_refinement U U' h b V hUV hU'V]
  rfl

variable (V' : B.Opens) (hV' : r ⁻¹ᵁ V' = s ⁻¹ᵁ V') (hV'V : V' ≤ V)
  (hUV' : U ≤ b ⁻¹ᵁ V')

include ht in
/-- The entire original relation still equalizes a section after its domain is shrunk. -/
theorem section_invariant_restriction :
    (r ∣_ V').appTop ((B.homOfLE hV'V).appTop t) =
      (s.resLE V' _ hV'.le).appTop ((B.homOfLE hV'V).appTop t) := by
  have he : s.resLE V' _ hV'.le ≫ B.homOfLE hV'V =
      C.homOfLE (r.preimage_mono hV'V) ≫ s.resLE V _ hV.le := by
    apply (cancel_mono V.ι).mp
    simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.resLE_comp_ι,
      Scheme.homOfLE_ι_assoc]
  change (((B.homOfLE hV'V).appTop ≫ (r ∣_ V').appTop) t) =
    (((B.homOfLE hV'V).appTop ≫ (s.resLE V' _ hV'.le).appTop) t)
  rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop,
    morphismRestrict_homOfLE, he, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
  exact congrArg (fun a ↦ (C.homOfLE (r.preimage_mono hV'V)).appTop a) ht

/-- Shrinking the original coefficient domain preserves the underlying endpoint morphism. -/
theorem openEndpoint_domain_refinement :
    openEndpoint b V' U hUV' ≫ B.homOfLE hV'V = openEndpoint b V U hUV := by
  apply (cancel_mono V.ι).mp
  simp only [openEndpoint, Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.resLE_comp_ι]

/-- Restricting an original section before pulling to a chart gives the same coefficient. -/
theorem invariantCoefficient_domain_refinement
    (ht' : (r ∣_ V').appTop ((B.homOfLE hV'V).appTop t) =
      (s.resLE V' _ hV'.le).appTop ((B.homOfLE hV'V).appTop t)) :
    invariantCoefficient ρ b r s z hr hs V' hV' U hU hUV'
        ((B.homOfLE hV'V).appTop t) ht' =
      invariantCoefficient ρ b r s z hr hs V hV U hU hUV t ht := by
  apply Subtype.ext
  simp only [invariantCoefficient_val]
  change (((B.homOfLE hV'V).appTop ≫ (openEndpoint b V' U hUV').appTop) t) = _
  rw [← Scheme.Hom.comp_appTop, openEndpoint_domain_refinement U b V hUV V' hV'V hUV']
  rfl

end FLT.Mazur.FiniteGroupOpenRelation
