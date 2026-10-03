/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonActionAssociativity
public import FLT.Mazur.ProjectiveLineActionTorus

/-!
# The whole-polygon action restricts to smooth multiplication

Identify the smooth open with the split group, compare on each pair of Laurent
components, and transport through the specified smooth-locus isomorphism.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
@[expose] public noncomputable section
universe u
namespace FLT.Mazur.PolygonActionSmooth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open PolygonPinching PolygonUniversalAction
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
variable {C : Over (Spec (.of K))} [LocallyOfFinitePresentation C.hom]
  (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
/-- Inclusion of the smooth open into the polygon. -/
def smoothι : smoothPolygon K (C := C) ⟶ C := Over.homMk C.hom.smoothLocus.ι rfl
/-- The split group identified with the smooth open of the polygon. -/
def smoothMap : G K n ⟶ C := (smoothIso K n hn p q h).inv ≫ smoothι K
@[reassoc] theorem component_smoothMap (a : ZMod n) :
    PolygonSplitGroup.component K n a ≫ smoothMap K n hn p q h =
      torusToComponent K ≫ componentι K n ((ZMod.finEquiv n).symm a) ≫ p := by
  apply Over.OverMorphism.ext
  simpa only [RingEquiv.apply_symm_apply, smoothMap, smoothι, PolygonSplitGroup.component,
    Over.comp_left, Over.homMk_left, Category.assoc] using
    component_smoothIso_inv K n hn p q h ((ZMod.finEquiv n).symm a)

theorem model_restriction : G K n ◁ smoothMap K n hn p q h ≫ act K n hn p q h =
    μ[G K n] ≫ smoothMap K n hn p q h := by
  apply PolygonSplitGroup.tensor_hom_ext (fun _ : ZMod n ↦ gm K) (fun _ : ZMod n ↦ gm K)
  intro a b
  change (PolygonSplitGroup.component K n a ⊗ₘ PolygonSplitGroup.component K n b) ≫ _ = _
  rw [tensorHom_comp_whiskerLeft_assoc, component_smoothMap,
    ← whiskerLeft_comp_tensorHom_assoc, component_act,
    ProjectiveLineActionTorus.torus_act_assoc, PolygonSplitGroup.component_mul_assoc,
    component_smoothMap]
  congr 3
  simp [rotateIndex, add_comm]

theorem smooth_restriction :
    let := smoothGrpObj K n hn p q h
    let := smoothCommGrpObj K n hn p q h
    ((smoothIso K n hn p q h).hom ⊗ₘ smoothι K) ≫ act K n hn p q h =
      μ[smoothPolygon K (C := C)] ≫ smoothι K := by
  let := smoothGrpObj K n hn p q h
  let := smoothCommGrpObj K n hn p q h
  change ((smoothIso K n hn p q h).hom ⊗ₘ smoothι K) ≫ act K n hn p q h =
    ((smoothIso K n hn p q h).hom ⊗ₘ (smoothIso K n hn p q h).hom) ≫
      μ[G K n] ≫ (smoothIso K n hn p q h).inv ≫ smoothι K
  have he := congrArg (((smoothIso K n hn p q h).hom ⊗ₘ
    (smoothIso K n hn p q h).hom) ≫ ·) (model_restriction K n hn p q h)
  simpa only [Category.assoc, tensorHom_comp_whiskerLeft_assoc, smoothMap,
    Iso.hom_inv_id_assoc] using he
end FLT.Mazur.PolygonActionSmooth
