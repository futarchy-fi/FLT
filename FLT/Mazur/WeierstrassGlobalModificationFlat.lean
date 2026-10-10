/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGlobalModificationZero
public import FLT.Mazur.WeierstrassModificationFlat
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Flatness of the entire modified projective cubic

The retained chart at infinity is flat over the original base, as is the
actual local modification. Their full open cover proves flatness of the
whole proper model. Its retained zero makes it a surjective family.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassGlobalModification
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) (hs : s ≠ 0)
open WeierstrassIntegralChart

/-- The unchanged infinity chart retains its original structure morphism. -/
@[reassoc] theorem infinityChart_structure :
    infinityChart W s b3 b4 b6 h3 h4 h6 hs ≫ structureMap W s b3 b4 b6 h3 h4 h6 hs =
      chartStructure W 1 := by
  rw [structureMap, infinityChart_contraction_assoc, integralCurveChart_structure]

/-- The whole local chart retains the existing modification structure morphism. -/
@[reassoc] theorem localChart_structure :
    localChart W s b3 b4 b6 h3 h4 h6 hs ≫ structureMap W s b3 b4 b6 h3 h4 h6 hs =
      WeierstrassModificationX.modificationStructure W s b3 b4 b6 h3 h4 h6 := by
  rw [structureMap, localChart_contraction_assoc]
  rfl

/-- The actual entire modified projective cubic is flat over the original Bezout domain. -/
instance structureMap_flat : Flat (structureMap W s b3 b4 b6 h3 h4 h6 hs) := by
  apply IsZariskiLocalAtSource.of_openCover (P := @Flat)
    (SchemeOpenReplacement.targetCover (affineBoundaryToY W) (boundary W s b3 b4 b6 h3 h4 h6 hs))
  intro i
  cases i with
  | false =>
    change Flat (infinityChart W s b3 b4 b6 h3 h4 h6 hs ≫
      structureMap W s b3 b4 b6 h3 h4 h6 hs)
    rw [infinityChart_structure]
    infer_instance
  | true =>
    change Flat (localChart W s b3 b4 b6 h3 h4 h6 hs ≫ structureMap W s b3 b4 b6 h3 h4 h6 hs)
    rw [localChart_structure]
    exact WeierstrassModificationX.structure_flat W s b3 b4 b6 h3 h4 h6 hs

variable [IsNoetherianRing R]

/-- Over a Noetherian base the flat proper family is universally open. -/
instance structureMap_universallyOpen :
    UniversallyOpen (structureMap W s b3 b4 b6 h3 h4 h6 hs) := UniversallyOpen.of_flat _

/-- Every base change is an open quotient onto the original base change. -/
theorem baseChange_openQuotient {S : Scheme.{u}} (f : S ⟶ Spec (.of R)) :
    IsOpenQuotientMap
      (CategoryTheory.Limits.pullback.snd (structureMap W s b3 b4 b6 h3 h4 h6 hs) f) :=
  ⟨(CategoryTheory.Limits.pullback.snd (structureMap W s b3 b4 b6 h3 h4 h6 hs) f).surjective,
    (CategoryTheory.Limits.pullback.snd (structureMap W s b3 b4 b6 h3 h4 h6 hs) f).continuous,
    (CategoryTheory.Limits.pullback.snd (structureMap W s b3 b4 b6 h3 h4 h6 hs) f).isOpenMap⟩

end FLT.Mazur.WeierstrassGlobalModification
