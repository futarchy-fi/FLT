/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.AmpleAffinePullback
public import FLT.Mazur.PolygonArithmeticBoundaryLine
public import FLT.Mazur.PolygonArithmeticStageLineQuotient
public import FLT.Mazur.SectionGradedLinePullback

/-!
# Actual adjacent boundary tensor-line quotients

The parameter-adic quotient of each boundary tensor power is the original
lower-stage tensor line pushed forward. The quotient projection recovers the
specified section pullback and line comparison in each degree.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonArithmeticStages

open FCurve ModuleLineBundleTensorPullback IdealAdicQuotient

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (A : Type) [CommRing A] (π : A) (m n : ℕ) (h : 2 ≤ n)

/-- The specified system line comparison on the original adjacent transition. -/
def adjacentBoundaryLineIso :
    (pullback (stageRestriction A π m n h)).obj (boundaryLine A π (m + 1) n h) ≅
      boundaryLine A π m n h := by
  simpa only [stageSystem, Functor.ofSequence_map_homOfLE_succ] using
    boundaryLineSystemIso A π n h (homOfLE (Nat.le_succ m))

/-- The actual adjacent tensor comparison in every degree. -/
def adjacentBoundaryTensorIso (d : ℕ) :
    (pullback (stageRestriction A π m n h)).obj
      (tensorPower (boundaryLine A π (m + 1) n h) d) ≅
        tensorPower (boundaryLine A π m n h) d :=
  tensorPowerIso (stageRestriction A π m n h) (boundaryLine A π (m + 1) n h) d ≪≫
    tensorPowerCongr (adjacentBoundaryLineIso A π m n h) d

/-- The quotient of the actual upper tensor line is the pushed-forward lower tensor line. -/
def boundaryTensorQuotientIso (d : ℕ) :
    quotient (stageParameterIdeal A π (m + 1) n h)
      (tensorPower (boundaryLine A π (m + 1) n h) d) (m + 1) ≅
    (pushforward (stageRestriction A π m n h)).obj (tensorPower (boundaryLine A π m n h) d) :=
  stageLineQuotientIso A π m n h _ ((boundaryLine_rankOne A π (m + 1) n h).tensorPower d) ≪≫
    (pushforward (stageRestriction A π m n h)).mapIso (adjacentBoundaryTensorIso A π m n h d)

/-- The quotient projection is the original specified tensor-degree section pullback. -/
@[reassoc] theorem projection_boundaryTensorQuotientIso (d : ℕ) :
    projection (stageParameterIdeal A π (m + 1) n h)
      (tensorPower (boundaryLine A π (m + 1) n h) d) (m + 1) ≫
      (boundaryTensorQuotientIso A π m n h d).hom =
    SectionGradedLinePullback.powerMap (stageRestriction A π m n h)
      (adjacentBoundaryLineIso A π m n h) d := by
  rw [boundaryTensorQuotientIso, Iso.trans_hom, ← Category.assoc,
    projection_stageLineQuotientIso]
  simp only [adjacentBoundaryTensorIso, Functor.mapIso_hom, Iso.trans_hom, Functor.map_comp,
    SectionGradedLinePullback.powerMap, SectionGradedPullback.powerMap,
    Adjunction.homEquiv_apply, Category.assoc]

end FLT.Mazur.PolygonArithmeticStages
