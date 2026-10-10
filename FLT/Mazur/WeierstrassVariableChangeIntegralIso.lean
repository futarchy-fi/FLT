/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassVariableChangeIntegralMorphism
public import FLT.Mazur.WeierstrassVariableChangeProjectiveInverse

/-!
# Admissible changes give isomorphisms of the original proper cubics

The inverse change supplies the inverse global map. Both composites are
identities because their composites with the closed projective embeddings are.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassCurve

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R]

/-- The regular map with an explicitly named transformed equation. -/
def integralVariableChangeTo (W V : WeierstrassCurve R) (C : VariableChange R)
    (h : C • W = V) : integralCurve V ⟶ integralCurve W := by
  subst V
  exact integralVariableChangeMap W C

/-- The named-target morphism retains the actual ambient projective formula. -/
@[reassoc] theorem integralVariableChangeTo_projectiveMap
    (W V : WeierstrassCurve R) (C : VariableChange R) (h : C • W = V) :
    integralVariableChangeTo W V C h ≫ integralProjectiveMap W =
      integralProjectiveMap V ≫ (WeierstrassVariableChangeLinear.projectiveIso C).hom := by
  subst V
  exact integralVariableChangeMap_projectiveMap W C

/-- The named-target morphism is over the coefficient scheme. -/
@[reassoc] theorem integralVariableChangeTo_structure
    (W V : WeierstrassCurve R) (C : VariableChange R) (h : C • W = V) :
    integralVariableChangeTo W V C h ≫ integralCurveStructure W =
      integralCurveStructure V := by
  subst V
  exact integralVariableChangeMap_structure W C

/-- An admissible change extends to an actual isomorphism of the entire integral cubic. -/
def integralVariableChangeIso (W V : WeierstrassCurve R) (C : VariableChange R)
    (h : C • W = V) : integralCurve V ≅ integralCurve W where
  hom := integralVariableChangeTo W V C h
  inv := integralVariableChangeTo V W C⁻¹ (by rw [← h, inv_smul_smul])
  hom_inv_id := by
    apply (cancel_mono (integralProjectiveMap V)).mp
    rw [Category.assoc, integralVariableChangeTo_projectiveMap,
      integralVariableChangeTo_projectiveMap_assoc,
      WeierstrassVariableChangeLinear.projectiveIso_hom_inv,
      Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (integralProjectiveMap W)).mp
    rw [Category.assoc, integralVariableChangeTo_projectiveMap,
      integralVariableChangeTo_projectiveMap_assoc,
      WeierstrassVariableChangeLinear.projectiveIso_inv, Iso.symm_hom, Iso.inv_hom_id,
      Category.comp_id, Category.id_comp]

/-- The original proper cubics are isomorphic over the original base. -/
def integralVariableChangeOverIso (W V : WeierstrassCurve R) (C : VariableChange R)
    (h : C • W = V) :
    Over.mk (integralCurveStructure V) ≅ Over.mk (integralCurveStructure W) :=
  Over.isoMk (integralVariableChangeIso W V C h) (integralVariableChangeTo_structure W V C h)

end FLT.Mazur.WeierstrassIntegralChart
