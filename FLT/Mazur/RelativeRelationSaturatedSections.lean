/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationSaturationCover
public import FLT.Mazur.RelativeRelationInvariantSectionRings
public import FLT.Mazur.SchemeEffectiveEpiSections
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Invariant regular functions are detected on a generating open

The original etale endpoint cover detects regular functions on the saturation.
For invariant functions, equality already on the unsaturated generating open
suffices. Thus passing to the saturation does not lose function-level evidence.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace FLT.Mazur.RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} {A U : Over S} {p q : A ⟶ U}
  (e : CategoryTheory.EquivalenceRelation p q) (hq : IsOpenMap q.left)
  (W : U.left.Opens)
local notation "Z" => Subtype.val (saturateOpen e hq W)

/-- The original second endpoint detects sections on the saturated source domain. -/
theorem saturation_appLE_injective [Etale q.left] :
    Function.Injective (q.left.appLE Z (p.left ⁻¹ᵁ W) (saturationCover_domain_le e hq W)) := by
  intro s t h
  apply (Z).topIso.symm.commRingCatIsoToRingEquiv.injective
  apply SchemeEffectiveEpiSections.appTop_injective (saturationCover e hq W)
  change (q.left.resLE Z (p.left ⁻¹ᵁ W) _).appTop ((Z).topIso.inv s) =
    (q.left.resLE Z (p.left ⁻¹ᵁ W) _).appTop ((Z).topIso.inv t)
  simp only [Scheme.Hom.resLE_app_top, ConcreteCategory.comp_apply,
    Iso.inv_hom_id_apply, h]

/-- On the original arrow domain, invariance computes pullback using only the generating open. -/
theorem saturatedInvariant_pullback
    (s : originalInvariantSections (p := p) (q := q) Z (saturateOpen_preimage_eq e hq W)) :
    q.left.appLE Z (p.left ⁻¹ᵁ W) (saturationCover_domain_le e hq W) s.val =
      p.left.app W (U.left.presheaf.map (homOfLE (le_saturateOpen e hq W)).op s.val) := by
  let h := p.left.preimage_mono (le_saturateOpen e hq W)
  have hs₀ : p.left.app Z s.val =
      q.left.appLE Z (p.left ⁻¹ᵁ Z) (saturateOpen_preimage_eq e hq W).le s.val :=
    s.property
  have hs := congrArg (A.left.presheaf.map (homOfLE h).op) hs₀
  have hp : U.left.presheaf.map (homOfLE (le_saturateOpen e hq W)).op ≫ p.left.app W =
      p.left.appLE Z (p.left ⁻¹ᵁ W) h := by
    rw [← Scheme.Hom.appLE_eq_app, Scheme.Hom.map_appLE]
  change (p.left.app Z ≫ A.left.presheaf.map (homOfLE h).op) s.val =
    (q.left.appLE Z (p.left ⁻¹ᵁ Z) _ ≫ A.left.presheaf.map (homOfLE h).op) s.val at hs
  rw [Scheme.Hom.appLE_map] at hs
  change (p.left.appLE Z (p.left ⁻¹ᵁ W) h) s.val = _ at hs
  rw [← hp] at hs
  exact hs.symm

/-- Restriction to the generating open detects all invariant regular functions on its saturation. -/
theorem saturatedInvariant_restriction_injective [Etale q.left] :
    Function.Injective (fun s : originalInvariantSections (p := p) (q := q) Z
      (saturateOpen_preimage_eq e hq W) ↦
        U.left.presheaf.map (homOfLE (le_saturateOpen e hq W)).op s.val) := by
  intro s t h
  apply Subtype.ext
  apply saturation_appLE_injective e hq W
  rw [saturatedInvariant_pullback, saturatedInvariant_pullback]
  exact congrArg (p.left.app W) h

/-- Actual invariant-sheaf sections restrict multiplicatively to the generating source open. -/
def saturatedSheafRestriction :
    (invariantSheaf e).obj.obj (op (orbitImageOpen e hq W)) →+* Γ(U.left, W) :=
  (U.left.presheaf.map (homOfLE (le_saturateOpen e hq W)).op).hom.comp
    ((invariantInclusion e).hom.app (op (orbitImageOpen e hq W))).hom

/-- The original quotient sheaf embeds in the regular functions of its generating open. -/
theorem saturatedSheafRestriction_injective [Etale q.left] :
    Function.Injective (saturatedSheafRestriction e hq W) := by
  intro s t h
  apply (invariantSectionRingEquiv e (orbitImageOpen e hq W)).injective
  apply saturatedInvariant_restriction_injective e hq W
  exact h

end FLT.Mazur.RelativeRelationOrbit
