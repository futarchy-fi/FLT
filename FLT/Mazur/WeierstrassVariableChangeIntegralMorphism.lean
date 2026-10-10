/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassVariableChangeLocalMorphism

/-!
# The regular coordinate-change morphism on the whole integral cubic

The local maps agree after the closed projective embedding, hence agree on
overlaps. Gluing extends the affine coordinate change across the origin.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)
  (C : WeierstrassCurve.VariableChange R)

/-- Every local output lies over the same ambient projective morphism. -/
@[reassoc] theorem variableChangeLocal_cover (p : Fin 3 × Fin 3) :
    variableChangeLocal W C p.1 p.2 ≫ integralProjectiveMap W =
      (variableChangeCover W C).f p ≫ integralProjectiveMap (C • W) ≫
        (WeierstrassVariableChangeLinear.projectiveIso C).hom := by
  rw [variableChangeLocal_projectiveMap]
  change _ = (PrincipalAffineRefinement.inclusion _ ≫ integralCurveChart _ _) ≫ _ ≫ _
  rw [Category.assoc, integralCurveChart_projectiveMap_assoc]

/-- The local morphisms agree on every actual categorical intersection. -/
theorem variableChangeLocal_compatible (p q : Fin 3 × Fin 3) :
    pullback.fst ((variableChangeCover W C).f p) ((variableChangeCover W C).f q) ≫
        variableChangeLocal W C p.1 p.2 =
      pullback.snd ((variableChangeCover W C).f p) ((variableChangeCover W C).f q) ≫
        variableChangeLocal W C q.1 q.2 := by
  apply (cancel_mono (integralProjectiveMap W)).mp
  simp only [Category.assoc, variableChangeLocal_cover]
  rw [← Category.assoc, ← Category.assoc, pullback.condition]
  simp only [Category.assoc]

/-- The global regular morphism from the transformed cubic to the original cubic. -/
def integralVariableChangeMap : integralCurve (C • W) ⟶ integralCurve W :=
  (variableChangeCover W C).glueMorphisms (fun p => variableChangeLocal W C p.1 p.2)
    (variableChangeLocal_compatible W C)

/-- Gluing retains the original principal-open formulas. -/
@[reassoc] theorem variableChangeCover_integralMap (p : Fin 3 × Fin 3) :
    (variableChangeCover W C).f p ≫ integralVariableChangeMap W C =
      variableChangeLocal W C p.1 p.2 :=
  (variableChangeCover W C).ι_glueMorphisms _ _ p

/-- The entire global map restricts the actual projective-space coordinate change. -/
@[reassoc] theorem integralVariableChangeMap_projectiveMap :
    integralVariableChangeMap W C ≫ integralProjectiveMap W =
      integralProjectiveMap (C • W) ≫
        (WeierstrassVariableChangeLinear.projectiveIso C).hom := by
  apply (variableChangeCover W C).hom_ext
  intro p
  rw [variableChangeCover_integralMap_assoc, variableChangeLocal_cover]

/-- The global cubic map is over the unchanged coefficient scheme. -/
@[reassoc] theorem integralVariableChangeMap_structure :
    integralVariableChangeMap W C ≫ integralCurveStructure W =
      integralCurveStructure (C • W) := by
  rw [← integralProjectiveMap_baseProjection, integralVariableChangeMap_projectiveMap_assoc,
    WeierstrassVariableChangeLinear.projectiveIso_baseProjection,
    integralProjectiveMap_baseProjection]

end FLT.Mazur.WeierstrassIntegralChart
