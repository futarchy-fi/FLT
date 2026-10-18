/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCyclicBoundaryStandardDivisor

/-!
# Individual marking lines on the chosen standard polygon

The specified polygon comparison preserves each complete marking factor and
its canonical section before taking products.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.PolygonCyclicBoundary
open PolygonPinching PolygonUniversalAction FCurve CyclicBoundaryParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonParameterTranslation.translationIso
  PolygonMarkingBaseChange.markingIdeal PolygonParameterTranslation.movedMarkingIdeal
variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (m : ℕ) [NeZero m] (hm : 0 < m) (n : ℕ) [NeZero n]
  (f : Over.mk (ProjectiveLineProductCharts.parameterToBase K L) ⟶
    CyclicBoundaryParameter.parameter (G K m) n) (a : Kˣ) (i : Fin m)
local notation "g" => ProjectiveLineProductCharts.parameterToBase K L
local notation "p" => PolygonAtlas.normalization K m
local notation "q" => PolygonAtlas.nodes K m
local notation "h" => PolygonAtlas.isPushout K m hm
local notation "e" => PolygonStandardFieldExtension.iso K L m hm

/-- The individual original marking line under the specified polygon comparison. -/
irreducible_def standardLabelLineComparison (j : Multiplicative (ZMod n)) :
    (Scheme.Modules.pullback (e).hom.left).obj
      (divisorLineBundle (labelIdeal K m hm (p) (q) (h) n (g) f a i j)
        (labelIdeal_cartier K m hm (p) (q) (h) n (g) f a i j).1) ≅
      divisorLineBundle (standardLabelIdeal K L m hm n f a i j)
        (standardLabelIdeal_cartier K L m hm n f a i j).1 :=
  divisorLinePullbackIsoOfCartier _
    (labelIdeal_cartier K m hm (p) (q) (h) n (g) f a i j).1
    (standardLabelIdeal_cartier K L m hm n f a i j).1

/-- Each original marking factor retains its canonical section on the standard polygon. -/
theorem standardLabelLineComparison_section (j : Multiplicative (ZMod n)) :
    DivisorLineSectionCompatible (e).hom.left
      (labelIdeal_cartier K m hm (p) (q) (h) n (g) f a i j).1
      (standardLabelIdeal_cartier K L m hm n f a i j).1
      (standardLabelLineComparison K L m hm n f a i j) := by
  rw [standardLabelLineComparison_def]
  exact divisorLinePullbackIsoOfCartier_section _ _ _

end FLT.Mazur.PolygonCyclicBoundary
