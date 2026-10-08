/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeAmbientCoefficient

/-!
# Equality transport for image coefficient transitions

General image-open maps retain their section maps under equality transport.
The concrete chart transitions have explicit transport and coordinate formulas.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

open ModuleSheafMorphismGluing ModuleSheafOpenImmersionLocalHom
open ModuleSheafOverlapImageTransition

/-- Reindexing a local isomorphism by an equality preserves all section maps. -/
lemma imageTransition_localApp_mpr {S : Scheme.{u}} {M N : S.Modules} {A B : S.Opens}
    (h : A = B) (e : M.over A ≅ N.over A) (W : S.Opens) (hW : W ≤ B) :
    localApp (Eq.mpr (congrArg (fun C ↦ M.over C ≅ N.over C) h.symm) e).hom hW =
      localApp e.hom (hW.trans_eq h.symm) := by
  subst B
  rfl

/-- Image extension and equality transport retain the original ambient section map. -/
lemma imageTransition_imageIso_mpr_app {S A B O : Scheme.{u}}
    (i : A ⟶ S) (j : B ⟶ S) [IsOpenImmersion i] [IsOpenImmersion j]
    (p : O ⟶ A) (q : O ⟶ B) (r : O ⟶ S) [IsOpenImmersion r]
    (hi : p ≫ i = r) (hj : q ≫ j = r) {M : A.Modules} {N : B.Modules}
    (e : (pullback p).obj M ≅ (pullback q).obj N)
    (V : S.Opens) (h : r.opensRange = V) (W : S.Opens) (hW : W ≤ V) :
    localApp (Eq.mpr (congrArg (fun C ↦
      ((pushforward i).obj M).over C ≅ ((pushforward j).obj N).over C) h.symm)
      (imageIso i j p q r hi hj e)).hom hW =
        localApp (localHom r (ambientIso i j p q r hi hj e).hom) (hW.trans_eq h.symm) := by
  rw [imageTransition_localApp_mpr h, imageIso_hom]

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

attribute [local instance] relativeTensorChart_isOpenImmersion
attribute [local irreducible] Scheme.Modules.pullback relativeChartCoefficientSheaf
attribute [local irreducible] relativeOverlapCoefficientIso relativeTensorChart
attribute [local irreducible] relativeOverlapAmbientCoefficientIso localHom

omit [IsLocallyNoetherian X] [IsAffine Y] in
/-- The pair image intersection is exactly the overlap immersion's image. -/
lemma relativeOverlapToScheme_opensRange (U V : X.affineOpens) :
    (relativeOverlapToScheme J f U V).opensRange =
      relativeTensorImageOpen J f U ⊓ relativeTensorImageOpen J f V :=
  TopologicalSpace.Opens.ext (relativeOverlapToScheme_range J f U V)

/-- The chart transition is precisely equality transport of the overlap image isomorphism. -/
lemma relativeChartCoefficientImageTransition_eq (U V : X.affineOpens) :
    relativeChartCoefficientImageTransition J f U V =
      Eq.mpr (congrArg (fun A ↦
        ((pushforward (relativeTensorChart J f U)).obj
          (relativeChartCoefficientSheaf J f U)).over A ≅
        ((pushforward (relativeTensorChart J f V)).obj
          (relativeChartCoefficientSheaf J f V)).over A)
        (relativeOverlapToScheme_opensRange J f U V).symm)
        (imageIso (relativeTensorChart J f U) (relativeTensorChart J f V)
          (relativeOverlapFirstProjection J f U V) (relativeOverlapSecondProjection J f U V)
          (relativeOverlapToScheme J f U V) rfl Limits.pullback.condition.symm
          (relativeOverlapCoefficientIso J f U V)) := rfl

/-- The ambient overlap isomorphism has its specified conjugated coordinate map. -/
lemma relativeOverlapAmbientCoefficientIso_hom_eq (U V : X.affineOpens) :
    (relativeOverlapAmbientCoefficientIso J f U V).hom =
      (ambientIso (relativeTensorChart J f U) (relativeTensorChart J f V)
        (relativeOverlapFirstProjection J f U V) (relativeOverlapSecondProjection J f U V)
        (relativeOverlapToScheme J f U V) rfl Limits.pullback.condition.symm
        (relativeOverlapCoefficientIso J f U V)).hom := by
  unfold relativeOverlapAmbientCoefficientIso
  rfl

end FLT.Mazur.IdealAdicGradedPullback
