/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.BlowupReesRatioTransition
public import FLT.Mazur.WeierstrassModificationReesContraction

/-!
# The actual scale and horizontal transitions commute in Rees Proj

The existing equation transition retains every original cubic function.
Uniqueness on the full fraction ratio open identifies it with the canonical
Rees transition and proves the required Proj gluing square.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassModificationReesCoordinates

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s : R)

local notation "A" => WeierstrassIntegralChart.Coordinate W 2
local notation "I" => WeierstrassDilatation.modificationCenter W s
local notation "ox" => WeierstrassIntegralChart.coord W 2 0

/-- The scale fraction chart included in Proj of the original center's Rees algebra. -/
def scaleProjInclusion : Spec (.of (WeierstrassDilatation.scaleReesChart W s)) ⟶
    BlowupRees.proj I :=
  BlowupRees.fractionChartInclusion I (algebraMap R A s) (Ideal.subset_span (by simp))

/-- The horizontal fraction chart included in the same original Rees Proj. -/
def horizontalProjInclusion :
    Spec (.of (WeierstrassModificationX.horizontalReesChart W s)) ⟶ BlowupRees.proj I :=
  BlowupRees.fractionChartInclusion I ox (Ideal.subset_span (by simp))

variable [IsDomain R] (b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) (hs : s ≠ 0)

/-- The existing scale/horizontal transition preserves every original cubic function. -/
theorem scaleHorizontalTransition_original (z : A) :
    scaleHorizontalTransition W s b3 b4 b6 h3 h4 h6 hs
      (algebraMap _ (ScaleHorizontalOpen W s) (scaleOriginalMap W s z)) =
        algebraMap _ (HorizontalScaleOpen W s) (horizontalOriginalMap W s z) := by
  have hs0 : WeierstrassDilatation.scaleReesChartEquiv W s b3 b4 b6 h3 h4 h6
      (IsRegular.of_ne_zero hs) (WeierstrassDilatation.fromOriginal W s b3 b4 b6 h3 h4 h6 z) =
        scaleOriginalMap W s z :=
    Subtype.ext (WeierstrassDilatation.scaleReesChartEquiv_fromOriginal
      W s b3 b4 b6 h3 h4 h6 (IsRegular.of_ne_zero hs) z)
  have hx0 : WeierstrassModificationX.horizontalReesChartEquiv W s b3 b4 b6 h3 h4 h6 hs
      (WeierstrassModificationX.fromOriginal W s b3 b4 b6 h3 h4 h6 z) =
        horizontalOriginalMap W s z :=
    Subtype.ext (WeierstrassModificationX.horizontalReesChartEquiv_fromOriginal
      W s b3 b4 b6 h3 h4 h6 hs z)
  rw [← hs0, scaleHorizontalTransition_base, ← hx0, ← horizontalScaleOpenEquiv_base]
  congr 1
  exact AlgHom.congr_fun (WeierstrassModificationX.dividedOverlapMap_fromOriginal
    W s b3 b4 b6 h3 h4 h6
    (IsScalarTower.toAlgHom R _ (WeierstrassModificationX.XOpen W s b3 b4 b6))
    (WeierstrassModificationX.xOpenUnit W s b3 b4 b6)
    (WeierstrassModificationX.xOpenUnit_val W s b3 b4 b6).symm) z

/-- The actual scale/horizontal substitution gives the required full Proj overlap square. -/
@[reassoc] theorem horizontalOverlap_toProj :
    horizontalOverlapToScale W s b3 b4 b6 h3 h4 h6 hs ≫ scaleProjInclusion W s =
      horizontalOpenInclusion W s ≫ horizontalProjInclusion W s := by
  rw [horizontalOverlapToScale_def, fractionOverlapIso_def, Category.assoc]
  exact BlowupRees.originalPreservingTransition_inclusion I (algebraMap R A s)
    (Ideal.subset_span (by simp)) ox (Ideal.subset_span (by simp))
    (scaleHorizontalTransition W s b3 b4 b6 h3 h4 h6 hs).toRingHom
    (scaleHorizontalTransition_original W s b3 b4 b6 h3 h4 h6 hs)

end FLT.Mazur.WeierstrassModificationReesCoordinates
