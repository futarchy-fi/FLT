/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGlobalModificationProper

/-!
# The original zero section on the whole modified cubic

The unchanged chart at infinity contains the original zero point. It gives
an actual section of the new proper structure map and remains that same
point under contraction and arbitrary scheme base change.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.WeierstrassGlobalModification
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) (hs : s ≠ 0)
open WeierstrassIntegralChart

/-- The original point at infinity as an actual point of the whole modified cubic. -/
def zeroSection : Spec (.of R) ⟶ model W s b3 b4 b6 h3 h4 h6 hs :=
  Spec.map (CommRingCat.ofHom (chartInfinityEvaluation (S := R) W).toRingHom) ≫
    infinityChart W s b3 b4 b6 h3 h4 h6 hs

/-- Contraction retains the exact original zero point. -/
@[reassoc] theorem zeroSection_contraction :
    zeroSection W s b3 b4 b6 h3 h4 h6 hs ≫ contraction W s b3 b4 b6 h3 h4 h6 hs =
      integralCurveZero W := by
  rw [zeroSection, Category.assoc, infinityChart_contraction]
  rfl

/-- The retained zero point is an actual section over the whole coefficient scheme. -/
@[reassoc] theorem zeroSection_structure :
    zeroSection W s b3 b4 b6 h3 h4 h6 hs ≫ structureMap W s b3 b4 b6 h3 h4 h6 hs = 𝟙 _ := by
  rw [structureMap, zeroSection_contraction_assoc, integralCurveZero_structure]

/-- The whole modified projective model meets every fiber of the original base. -/
instance structureMap_surjective : Surjective (structureMap W s b3 b4 b6 h3 h4 h6 hs) := by
  constructor
  intro x
  refine ⟨zeroSection W s b3 b4 b6 h3 h4 h6 hs x, ?_⟩
  exact congrArg (fun f => f x) (zeroSection_structure W s b3 b4 b6 h3 h4 h6 hs)

variable {S : Scheme.{u}} (f : S ⟶ Spec (.of R))

/-- Arbitrary base change retains the original infinity section. -/
def baseChangeZero : S ⟶ pullback (structureMap W s b3 b4 b6 h3 h4 h6 hs) f :=
  pullback.lift (f ≫ zeroSection W s b3 b4 b6 h3 h4 h6 hs) (𝟙 S) (by
    rw [Category.assoc, zeroSection_structure, Category.comp_id, Category.id_comp])

/-- The retained section remains a section after arbitrary base change. -/
@[reassoc] theorem baseChangeZero_structure :
    baseChangeZero W s b3 b4 b6 h3 h4 h6 hs f ≫
      pullback.snd (structureMap W s b3 b4 b6 h3 h4 h6 hs) f = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- Every scheme base change of the whole model is a closed surjection. -/
theorem baseChange_closedSurjective :
    IsClosedMap (pullback.snd (structureMap W s b3 b4 b6 h3 h4 h6 hs) f) ∧
      Function.Surjective (pullback.snd (structureMap W s b3 b4 b6 h3 h4 h6 hs) f) :=
  ⟨(pullback.snd (structureMap W s b3 b4 b6 h3 h4 h6 hs) f).isClosedMap,
    (pullback.snd (structureMap W s b3 b4 b6 h3 h4 h6 hs) f).surjective⟩

end FLT.Mazur.WeierstrassGlobalModification
