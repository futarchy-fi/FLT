/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassVariableChangeAffineProduct
public import FLT.Mazur.WeierstrassVariableChangeAffineRestriction
public import FLT.Mazur.WeierstrassIntegralCurveProduct

/-!
# The actual proper product morphism of an admissible change

The proper isomorphism acts on both inputs of the fiber product. Its
restriction is the previously constructed affine product substitution.
-/

@[expose] public noncomputable section

open WeierstrassCurve CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (W V : WeierstrassCurve R)
  (C : VariableChange R) (h : C • W = V)

/-- Apply the actual proper change to both inputs of the original fiber product. -/
def integralVariableChangeProduct : integralCurveProduct V ⟶ integralCurveProduct W :=
  pullback.lift
    (pullback.fst _ _ ≫ (integralVariableChangeIso W V C h).hom)
    (pullback.snd _ _ ≫ (integralVariableChangeIso W V C h).hom) (by
      simp only [Category.assoc, integralVariableChangeIso,
        integralVariableChangeTo_structure, pullback.condition])

/-- The first projection retains the actual proper isomorphism. -/
@[reassoc] theorem integralVariableChangeProduct_fst :
    integralVariableChangeProduct W V C h ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ (integralVariableChangeIso W V C h).hom := pullback.lift_fst ..

/-- The second projection retains the same proper isomorphism. -/
@[reassoc] theorem integralVariableChangeProduct_snd :
    integralVariableChangeProduct W V C h ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ (integralVariableChangeIso W V C h).hom := pullback.lift_snd ..

/-- The affine product map retains the first actual affine isomorphism. -/
theorem affineProductVariableChange_spec_left :
    Spec.map (CommRingCat.ofHom (affineProductVariableChange W V C h).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (productLeft W).toRingHom) =
      Spec.map (CommRingCat.ofHom (productLeft V).toRingHom) ≫
        (affineVariableChangeIso W V C h).hom := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom))
    (affineProductVariableChange_left W V C h)

/-- The affine product map retains the second actual affine isomorphism. -/
theorem affineProductVariableChange_spec_right :
    Spec.map (CommRingCat.ofHom (affineProductVariableChange W V C h).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (productRight W).toRingHom) =
      Spec.map (CommRingCat.ofHom (productRight V).toRingHom) ≫
        (affineVariableChangeIso W V C h).hom := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom))
    (affineProductVariableChange_right W V C h)

/-- The full product morphism restricts to the original affine substitution on both inputs. -/
@[reassoc] theorem integralVariableChangeProduct_affine :
    integralCurveProductChart V false false ≫ integralVariableChangeProduct W V C h =
      Spec.map (CommRingCat.ofHom (affineProductVariableChange W V C h).toRingHom) ≫
        integralCurveProductChart W false false := by
  apply pullback.hom_ext
  · simp only [Category.assoc, integralVariableChangeProduct_fst,
      integralCurveProductChart_fst]
    rw [← Category.assoc, integralCurveProductChart_fst, Category.assoc]
    change Spec.map (CommRingCat.ofHom (productLeft V).toRingHom) ≫
      integralCurveChart V 2 ≫ (integralVariableChangeIso W V C h).hom = _
    rw [integralVariableChangeIso_affine, ← Category.assoc]
    exact congrArg (· ≫ integralCurveChart W 2)
      (affineProductVariableChange_spec_left W V C h).symm
  · simp only [Category.assoc, integralVariableChangeProduct_snd,
      integralCurveProductChart_snd]
    rw [← Category.assoc, integralCurveProductChart_snd, Category.assoc]
    change Spec.map (CommRingCat.ofHom (productRight V).toRingHom) ≫
      integralCurveChart V 2 ≫ (integralVariableChangeIso W V C h).hom = _
    rw [integralVariableChangeIso_affine, ← Category.assoc]
    exact congrArg (· ≫ integralCurveChart W 2)
      (affineProductVariableChange_spec_right W V C h).symm

end FLT.Mazur.WeierstrassIntegralChart
