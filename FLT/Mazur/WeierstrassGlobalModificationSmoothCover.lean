/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGlobalModificationFractionCover
public import FLT.Mazur.WeierstrassModifiedSmoothTotalCover

/-!
# The complete single-step modified smooth source cover

The original infinity chart and all three original fraction charts cover the
modified second input. On each product, refine by every original output chart
and then by affine opens. In the fraction cases the chosen contraction is
exactly the one used by the constructed local action lifts.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassGlobalModification

open WeierstrassIntegralChart WeierstrassModificationReesCoordinates
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) (hs : s ≠ 0)

/-- Chosen original contractions of every entire input chart. -/
def originalInputContraction (i : Option (Fin 3)) :
    Spec (originalFractionCoverRing W s i) ⟶ integralCurve W :=
  match i with
  | none => integralCurveChart W 1
  | some j => fractionSmoothContraction W s (centerGenerators W s j)

/-- The actual input-cover maps retain the chosen original contractions. -/
theorem originalInputContraction_eq (i : Option (Fin 3)) :
    (originalFractionCover W s b3 b4 b6 h3 h4 h6 hs).f i ≫
        contraction W s b3 b4 b6 h3 h4 h6 hs = originalInputContraction W s i := by
  cases i with
  | none => exact originalFractionCoverMap_none_contraction W s b3 b4 b6 h3 h4 h6 hs
  | some j => exact originalFractionCoverMap_some_contraction W s b3 b4 b6 h3 h4 h6 hs j

/-- The whole modified smooth-input product, including exceptional and infinity points. -/
abbrev smoothActionProduct :=
  modifiedSmoothProduct W (contraction W s b3 b4 b6 h3 h4 h6 hs)

/-- The complete affine input/output cover of the actual single-step action source. -/
def smoothActionCover : (smoothActionProduct W s b3 b4 b6 h3 h4 h6 hs).AffineOpenCover :=
  modifiedSmoothTotalCover W (contraction W s b3 b4 b6 h3 h4 h6 hs)
    (originalFractionCover W s b3 b4 b6 h3 h4 h6 hs) (originalInputContraction W s)
    (originalInputContraction_eq W s b3 b4 b6 h3 h4 h6 hs)

/-- The contracted original action on the entire single-step product. -/
def smoothActionOriginal :
    smoothActionProduct W s b3 b4 b6 h3 h4 h6 hs ⟶ integralCurve W :=
  modifiedSmoothAddition W (contraction W s b3 b4 b6 h3 h4 h6 hs)

/-- Every cover member retains the original action on its assigned entire input chart. -/
@[reassoc] theorem smoothActionCover_original
    (i : (smoothActionCover W s b3 b4 b6 h3 h4 h6 hs).I₀) :
    (smoothActionCover W s b3 b4 b6 h3 h4 h6 hs).f i ≫
        smoothActionOriginal W s b3 b4 b6 h3 h4 h6 hs =
      (modifiedSmoothAffineCover W (originalInputContraction W s i.1)).f i.2 ≫
        modifiedSmoothAffineAddition W (originalInputContraction W s i.1) :=
  modifiedSmoothTotalCover_addition W (contraction W s b3 b4 b6 h3 h4 h6 hs)
    (originalFractionCover W s b3 b4 b6 h3 h4 h6 hs) (originalInputContraction W s)
    (originalInputContraction_eq W s b3 b4 b6 h3 h4 h6 hs) i

/-- All points of the entire source have one of the constructed affine presentations. -/
theorem smoothActionCover_covers (z : smoothActionProduct W s b3 b4 b6 h3 h4 h6 hs) :
    ∃ (i : (smoothActionCover W s b3 b4 b6 h3 h4 h6 hs).I₀)
      (x : Spec ((smoothActionCover W s b3 b4 b6 h3 h4 h6 hs).X i)),
      (smoothActionCover W s b3 b4 b6 h3 h4 h6 hs).f i x = z :=
  (smoothActionCover W s b3 b4 b6 h3 h4 h6 hs).openCover.exists_eq z

end FLT.Mazur.WeierstrassGlobalModification
