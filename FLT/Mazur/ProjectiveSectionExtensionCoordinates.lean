/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveSectionExtensionCharts
public import FLT.Mazur.ProjectiveTwistTensor

/-!
# Ambient coordinates for projective section extension

Coordinate-ring scalars on chart intersections agree with the transition
sections of the twisting sheaf. Tensor trivializations are transported to
ambient opens, where both coordinates and inverse coordinates commute with
restriction. The chart numerators therefore agree in twisted coordinates on
their intersections with the original chart.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite MvPolynomial

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace FLT.Mazur.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)

attribute [local instance] MvPolynomial.gradedAlgebra

private lemma iso_inv_appIso {X Y : Scheme.{u}} (e : X ≅ Y) (V : Y.Opens) :
    (e.inv.appIso V).inv = e.hom.appLE V (e.inv ''ᵁ V) (by
      simp only [Scheme.Hom.inv_image]
      exact le_rfl) := by
  rw [← cancel_mono (e.inv.appIso V).hom, Iso.inv_hom_id,
    Scheme.Hom.appIso_hom']
  rw [Scheme.Hom.appLE_comp_appLE]
  simp only [e.inv_hom_id]
  change 𝟙 _ = 𝟙 _ ≫ Y.presheaf.map (𝟙 _)
  rw [Category.id_comp]
  exact (Y.presheaf.map_id _).symm

/-- The overlap scalar map is the homogeneous-localization section map. -/
lemma overlapScalarHom_eq (i j : ι) :
    overlapScalarHom R ι i j =
      ((Proj.awayToSection (grading R ι) (X i * X j)) ≫
        (space R ι).presheaf.map (homOfLE (chart_inf R ι i j).le).op).hom := by
  unfold overlapScalarHom overlapMap
  rw [Scheme.Hom.comp_appIso]
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, eqToIso.inv,
    Scheme.Opens.ι_appIso, Iso.refl_inv]
  rw [iso_inv_appIso]
  simp only [Scheme.Hom.appLE]
  simp only [← Category.assoc]
  rw [show (overlapIso R ι i j).hom =
    Proj.basicOpenToSpec (grading R ι) (X i * X j) from rfl]
  rw [Proj.basicOpenToSpec_app_top]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simp only [Scheme.Opens.topIso_inv, ← Functor.map_comp]
  congr 2

/-- The localized coordinate ratio is exactly the degree-one transition scalar. -/
lemma overlapScalarHom_coordinate (i j : ι) :
    overlapScalarHom R ι i j (toOverlap R ι i j (coordinate R ι i j)) =
      (twistTransition R ι 1 i j : Γ(space R ι, chart R ι i ⊓ chart R ι j)) := by
  rw [overlapScalarHom_eq]
  change _ = (space R ι).presheaf.map (homOfLE (chart_inf R ι i j).le).op
    ((Proj.awayToSection (grading R ι) (X i * X j)).hom
      (transitionUnit R ι 1 i j : overlapRing R ι i j))
  rw [transitionUnit_one, ratioUnit_val]
  rfl

/-- Powers of coordinate scalars give the positive-degree transition units. -/
lemma overlapScalarHom_coordinate_pow (i j : ι) (N : ℕ) :
    overlapScalarHom R ι i j (toOverlap R ι i j (coordinate R ι i j) ^ N) =
      (twistTransition R ι (N : ℤ) i j :
        Γ(space R ι, chart R ι i ⊓ chart R ι j)) := by
  rw [map_pow, overlapScalarHom_coordinate]
  simp only [twistTransition, transitionSection, transitionUnit, zpow_one,
    zpow_natCast, map_pow, Units.val_pow_eq_pow_val]

open FLT.Mazur.FCurve ModuleSheafTensor

/-- Sections on an open subscheme identified with sections on the ambient open. -/
def ambientSectionsIso (F : (space R ι).Modules) (V : (space R ι).Opens) :
    Γ(F.restrict V.ι, ⊤) ≅ Γ(F, V) :=
  F.restrictAppIso V.ι ⊤ ≪≫
    F.presheaf.mapIso (eqToIso V.ι_image_top.symm).op

/-- The ambient comparison transports the scalar action by the top-open ring iso. -/
lemma ambientSectionsIso_smul (F : (space R ι).Modules) (V : (space R ι).Opens)
    (r : Γ(V.toScheme, ⊤)) (m : Γ(F.restrict V.ι, ⊤)) :
    (ambientSectionsIso R ι F V).hom (r • m) =
      V.topIso.hom r • (ambientSectionsIso R ι F V).hom m := by
  change F.presheaf.map (eqToHom V.ι_image_top.symm).op
    ((V.ι.appIso ⊤).inv r • (show Γ(F, V.ι ''ᵁ ⊤) from m)) = _
  erw [F.val.map_smul]
  rw [Scheme.Opens.ι_appIso]
  rfl

/-- Tensor coordinates with both source and target on the ambient projective space. -/
def twistAmbientIso (F : (space R ι).Modules) (d : ℤ) (i : ι)
    (V : (space R ι).Opens) (hi : V ≤ chart R ι i) :
    Γ(twistTensor R ι F d, V) ≅ Γ(F, V) :=
  (ambientSectionsIso R ι (twistTensor R ι F d) V).symm ≪≫
    (sectionsCongr (twistTensorOnOpenIso R ι F d i V hi) ⊤).toAddEquiv.toAddCommGrpIso ≪≫
      ambientSectionsIso R ι F V

/-- Inverse ambient coordinates tensor with the basis defined by the cocycle. -/
lemma twistAmbientIso_inv (F : (space R ι).Modules) (d : ℤ) (i : ι)
    (V : (space R ι).Opens) (hi : V ≤ chart R ι i) (m : Γ(F, V)) :
    (twistAmbientIso R ι F d i V hi).inv m =
      pure F (twistingSheaf R ι d) V m ((twistCocycle R ι d).extend i hi 1) := by
  change F.presheaf.obj (op V) at m
  change (twistTensor R ι F d).presheaf.map (eqToHom V.ι_image_top.symm).op
    ((twistTensorOnOpenIso R ι F d i V hi).inv.app ⊤
      (F.presheaf.map (eqToHom V.ι_image_top).op m)) = _
  rw [twistTensorOnOpenIso_inv]
  change (twistTensor R ι F d).presheaf.map (eqToHom V.ι_image_top.symm).op
    (pure F (twistingSheaf R ι d) _
      (F.presheaf.map (eqToHom V.ι_image_top).op m)
      ((twistCocycle R ι d).extend i ((V.ι_image_le ⊤).trans hi) 1)) = _
  erw [pure_restrict]
  apply congrArg₂ (pure F (twistingSheaf R ι d) V)
  · simp only [← Functor.map_comp_apply, ← op_comp, eqToHom_trans,
      eqToHom_refl, op_id]
    exact ConcreteCategory.congr_hom (F.presheaf.map_id _) m
  · exact ((twistCocycle R ι d).extend_restrict i _ V.ι_image_top.symm.le 1).trans
      (by rw [map_one])

/-- Inverse coordinates commute with restriction of ambient opens. -/
lemma twistAmbientIso_inv_restrict (F : (space R ι).Modules) (d : ℤ) (i : ι)
    {V W : (space R ι).Opens} (hi : V ≤ chart R ι i) (h : W ≤ V) (m : Γ(F, V)) :
    (twistTensor R ι F d).presheaf.map (homOfLE h).op
      ((twistAmbientIso R ι F d i V hi).inv m) =
    (twistAmbientIso R ι F d i W (h.trans hi)).inv
      (F.presheaf.map (homOfLE h).op m) := by
  erw [twistAmbientIso_inv, pure_restrict, twistAmbientIso_inv]
  apply congrArg (pure F (twistingSheaf R ι d) W (F.presheaf.map (homOfLE h).op m))
  exact ((twistCocycle R ι d).extend_restrict i hi h 1).trans (by rw [map_one])

/-- Ambient coefficients commute with restriction. -/
lemma twistAmbientIso_hom_restrict (F : (space R ι).Modules) (d : ℤ) (i : ι)
    {V W : (space R ι).Opens} (hi : V ≤ chart R ι i) (h : W ≤ V)
    (s : Γ(twistTensor R ι F d, V)) :
    (twistAmbientIso R ι F d i W (h.trans hi)).hom
      ((twistTensor R ι F d).presheaf.map (homOfLE h).op s) =
    F.presheaf.map (homOfLE h).op ((twistAmbientIso R ι F d i V hi).hom s) := by
  apply (ConcreteCategory.bijective_of_isIso
    (twistAmbientIso R ι F d i W (h.trans hi)).inv).injective
  rw [← twistAmbientIso_inv_restrict R ι F d i hi h]
  simp only [← ConcreteCategory.comp_apply, Category.assoc, Iso.hom_inv_id,
    Category.comp_id, ConcreteCategory.id_apply]

/-- The ambient coefficients satisfy the twisting transition equation. -/
lemma twistAmbientIso_transition (F : (space R ι).Modules) (d : ℤ) (i j : ι)
    (V : (space R ι).Opens) (hi : V ≤ chart R ι i) (hj : V ≤ chart R ι j)
    (s : Γ(twistTensor R ι F d, V)) :
    (twistAmbientIso R ι F d i V hi).hom s =
      ((restrictUnits R ι (le_inf hi hj) (twistTransition R ι 1 i j) ^ d :
        Γ(space R ι, V)ˣ) : Γ(space R ι, V)) •
      (twistAmbientIso R ι F d j V hj).hom s := by
  have h := congrArg (ambientSectionsIso R ι F V).hom
    (twistTensor_transition R ι F d i j V hi hj ⊤
      ((ambientSectionsIso R ι (twistTensor R ι F d) V).inv s))
  rw [ambientSectionsIso_smul] at h
  have he : V.topIso.hom (show Γ(V.toScheme, ⊤) from
      ((restrictUnits R ι (le_inf ((V.ι_image_le ⊤).trans hi)
        ((V.ι_image_le ⊤).trans hj)) (twistTransition R ι 1 i j) ^ d :
        Γ(space R ι, V.ι ''ᵁ ⊤)ˣ) : Γ(space R ι, V.ι ''ᵁ ⊤))) =
      ((restrictUnits R ι (le_inf hi hj) (twistTransition R ι 1 i j) ^ d :
        Γ(space R ι, V)ˣ) : Γ(space R ι, V)) := by
    change ((restrictUnits R ι V.ι_image_top.symm.le
      (restrictUnits R ι (le_inf ((V.ι_image_le ⊤).trans hi)
        ((V.ι_image_le ⊤).trans hj)) (twistTransition R ι 1 i j) ^ d) :
      Γ(space R ι, V)ˣ) : Γ(space R ι, V)) = _
    rw [map_zpow, restrictUnits_comp]
  rw [he] at h
  exact h


/-- Changing ambient coordinates multiplies by the transition scalar. -/
lemma twistAmbientIso_change (F : (space R ι).Modules) (d : ℤ) (i j : ι)
    (V : (space R ι).Opens) (hi : V ≤ chart R ι i) (hj : V ≤ chart R ι j)
    (m : Γ(F, V)) :
    (twistAmbientIso R ι F d i V hi).hom
      ((twistAmbientIso R ι F d j V hj).inv m) =
      ((restrictUnits R ι (le_inf hi hj) (twistTransition R ι 1 i j) ^ d :
        Γ(space R ι, V)ˣ) : Γ(space R ι, V)) • m := by
  rw [twistAmbientIso_transition R ι F d i j V hi hj]
  rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id, ConcreteCategory.id_apply]

/-- Matching transition coefficients give equal inverse coordinates on a common open. -/
lemma twistAmbientIso_inv_eq (F : (space R ι).Modules) (d : ℤ) (i j : ι)
    (V : (space R ι).Opens) (hi : V ≤ chart R ι i) (hj : V ≤ chart R ι j)
    (m n : Γ(F, V))
    (h : m = ((restrictUnits R ι (le_inf hi hj) (twistTransition R ι 1 i j) ^ d :
      Γ(space R ι, V)ˣ) : Γ(space R ι, V)) • n) :
    (twistAmbientIso R ι F d i V hi).inv m =
      (twistAmbientIso R ι F d j V hj).inv n := by
  apply (ConcreteCategory.bijective_of_isIso (twistAmbientIso R ι F d i V hi).hom).injective
  rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id, ConcreteCategory.id_apply,
    twistAmbientIso_change R ι F d i j V hi hj]
  exact h

/-- Restricting a transition to its own overlap leaves its natural powers unchanged. -/
lemma twistTransition_restrict_self_pow (i j : ι) (N : ℕ) :
    ((restrictUnits R ι (le_inf inf_le_left inf_le_right)
      (twistTransition R ι 1 i j) ^ (N : ℤ) :
      Γ(space R ι, chart R ι i ⊓ chart R ι j)ˣ) :
      Γ(space R ι, chart R ι i ⊓ chart R ι j)) =
    (twistTransition R ι 1 i j : Γ(space R ι, chart R ι i ⊓ chart R ι j)) ^ N := by
  have hu : restrictUnits R ι (le_inf inf_le_left inf_le_right)
      (twistTransition R ι 1 i j) = twistTransition R ι 1 i j := by
    apply Units.ext
    exact ConcreteCategory.congr_hom ((space R ι).presheaf.map_id _)
      (twistTransition R ι 1 i j : Γ(space R ι, chart R ι i ⊓ chart R ι j))
  rw [hu, zpow_natCast, Units.val_pow_eq_pow_val]

/-- The chart numerators define twisted sections agreeing with `s` near its chart. -/
theorem sectionExtension_twistCoordinates [Finite ι]
    (F : (space R ι).Modules) [F.IsFinitePresentation]
    (i : ι) (s : Γ(F, chart R ι i)) :
    ∃ (N : ℕ) (t : ∀ j, Γ(F, chart R ι j)), t i = s ∧ ∀ j,
      (twistTensor R ι F (N : ℤ)).presheaf.map (homOfLE inf_le_left).op
        ((twistAmbientIso R ι F (N : ℤ) j (chart R ι j) le_rfl).inv (t j)) =
      (twistTensor R ι F (N : ℤ)).presheaf.map (homOfLE inf_le_right).op
        ((twistAmbientIso R ι F (N : ℤ) i (chart R ι i) le_rfl).inv s) := by
  obtain ⟨N, t, hi, ht⟩ := sectionExtension_openChartNumerators R ι F i s
  refine ⟨N, t, hi, fun j ↦ ?_⟩
  refine (twistAmbientIso_inv_restrict R ι F (N : ℤ) j le_rfl inf_le_left (t j)).trans ?_
  refine Eq.trans ?_
    (twistAmbientIso_inv_restrict R ι F (N : ℤ) i le_rfl inf_le_right s).symm
  apply twistAmbientIso_inv_eq
  rw [twistTransition_restrict_self_pow, ht j, overlapScalarHom_coordinate]

end FLT.Mazur.ProjectiveSpace
