/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeIdealOpenExtension

/-!
# Exact support ranges for relative ambient extension

The ambient open base change has its exact inverse-image range, and extension
of a finite family has precisely the image of the original family's support.
These point-set statements accompany, rather than replace, full ideal recovery.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.OpenIdealCover FLT.Mazur.FCurve

universe u

namespace FLT.Mazur.ClosedIdealCover

variable {A B S X : Scheme.{u}} (a : A ⟶ S) (b : B ⟶ S)
variable (i : A ⟶ B) (hi : i ≫ b = a) (s : X ⟶ S)

/-- The induced original ambient map has the exact inverse-image range. -/
theorem relativeIdealAmbientHom_range :
    Set.range (relativeIdealAmbientHom a b i hi s) = pullback.snd s b ⁻¹' Set.range i := by
  have h := relativeIdealAmbientHom_isPullback a b i hi s
  rw [← h.isoPullback_hom_fst]
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr h.isoPullback.hom.surjective, Set.image_univ,
    Scheme.Pullback.range_fst]

variable [IsOpenImmersion i] [IsSeparated b] (d : ℕ)

/-- Extension has exactly the image of the original closed family, with no extra support. -/
theorem relativeIdealFamilyExtension_range (J : RelativeIdealFamilies a d s) :
    Set.range (relativeIdealFamilyExtension a b i hi s d J).val.subschemeι =
      Set.range (J.val.subschemeι ≫ relativeIdealAmbientHom a b i hi s) := by
  let m := relativeIdealAmbientHom a b i hi s
  have h : FiniteLocallyFreeDegree (J.val.subschemeι ≫ m ≫ pullback.fst s b) d := by
    rw [relativeIdealAmbientHom_fst]
    exact J.property
  let _ := h.1
  let _ := finiteFamily_closed m (pullback.fst s b) J.val
  change Set.range (J.val.subschemeι ≫ m).imageι = Set.range (J.val.subschemeι ≫ m)
  conv_rhs => rw [← Scheme.Hom.toImage_imageι (J.val.subschemeι ≫ m)]
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr (J.val.subschemeι ≫ m).toImage.surjective, Set.image_univ]

end FLT.Mazur.ClosedIdealCover
