/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeClopenSectionExtension
public import FLT.Mazur.OpenCoverFullBoundaryDetection

/-!
# Pullback and full boundary control for extension by zero

Uniqueness on the two complementary opens proves naturality for arbitrary
scheme maps. Checking the original ideal subscheme on both opens proves
that extension preserves its full homogeneous boundary equation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeClopenSectionExtension
variable {X Y : Scheme.{0}} (U V : X.Opens)
  (hdis : U ⊓ V = ⊥) (hcover : U ⊔ V = ⊤)

include hdis in
/-- Complementary opens remain disjoint after any scheme pullback. -/
theorem preimage_disjoint (f : Y ⟶ X) : (f ⁻¹ᵁ U) ⊓ (f ⁻¹ᵁ V) = ⊥ := by
  change f ⁻¹ᵁ (U ⊓ V) = ⊥
  rw [hdis]
  rfl

include hcover in
/-- Complementary opens continue to cover after any scheme pullback. -/
theorem preimage_cover (f : Y ⟶ X) : (f ⁻¹ᵁ U) ⊔ (f ⁻¹ᵁ V) = ⊤ := by
  change f ⁻¹ᵁ (U ⊔ V) = ⊤
  rw [hcover]
  rfl

/-- Extension by zero commutes with every scheme map, without flatness. -/
theorem pullback_extend (f : Y ⟶ X) (s : Γ(U.toScheme, ⊤)) :
    f.appTop (extend U V hdis hcover s) =
      extend (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) (preimage_disjoint U V hdis f)
        (preimage_cover U V hcover f) ((f.resLE U _ le_rfl).appTop s) := by
  apply section_ext_pair (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) (preimage_cover U V hcover f)
  · rw [extend_left]
    change ((f ⁻¹ᵁ U).ι ≫ f).appTop _ = _
    rw [← Scheme.Hom.resLE_comp_ι f le_rfl]
    change (f.resLE U _ le_rfl).appTop (U.ι.appTop _) = _
    rw [extend_left]
  · rw [extend_right]
    change ((f ⁻¹ᵁ V).ι ≫ f).appTop _ = _
    rw [← Scheme.Hom.resLE_comp_ι f le_rfl]
    change (f.resLE V _ le_rfl).appTop (V.ι.appTop _) = _
    rw [extend_right, map_zero]

/-- Named maps on the complementary pieces suffice for naturality of full sections. -/
theorem pullback_extend_of_squares (U' V' : Y.Opens)
    (hd : U' ⊓ V' = ⊥) (hc : U' ⊔ V' = ⊤) (f : Y ⟶ X)
    (g : U'.toScheme ⟶ U.toScheme) (h : V'.toScheme ⟶ V.toScheme)
    (hg : g ≫ U.ι = U'.ι ≫ f) (hh : h ≫ V.ι = V'.ι ≫ f)
    (s : Γ(U.toScheme, ⊤)) :
    f.appTop (extend U V hdis hcover s) = extend U' V' hd hc (g.appTop s) := by
  apply section_ext_pair U' V' hc
  · rw [extend_left]
    change (U'.ι ≫ f).appTop _ = _
    rw [← hg]
    change g.appTop (U.ι.appTop _) = _
    rw [extend_left]
  · rw [extend_right]
    change (V'.ι ≫ f).appTop _ = _
    rw [← hh]
    change h.appTop (V.ι.appTop _) = _
    rw [extend_right, map_zero]

/-- Full ideal boundary vanishing survives extension by zero, including nilpotent values. -/
theorem extend_boundary_zero (I : X.IdealSheafData) (s : Γ(U.toScheme, ⊤))
    (hs : (I.comap U.ι).subschemeι.appTop s = 0) :
    I.subschemeι.appTop (extend U V hdis hcover s) = 0 := by
  apply OpenCoverFullBoundaryDetection.boundary_zero_of_local
    (fun b : Bool ↦ if b then U else V) (by
      simp only [iSup_bool_eq, Bool.false_eq_true, ite_false, ite_true]
      exact hcover)
  intro b
  cases b
  · change (I.comap V.ι).subschemeι.appTop (V.ι.appTop _) = 0
    rw [extend_right, map_zero]
  · change (I.comap U.ι).subschemeι.appTop (U.ι.appTop _) = 0
    rw [extend_left]
    exact hs

end FLT.Mazur.SchemeClopenSectionExtension
