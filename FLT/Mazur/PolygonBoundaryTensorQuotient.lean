/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleAffinePullback
public import FLT.Mazur.PolygonInfinitesimalStageLine
public import FLT.Mazur.PolygonStageLineQuotient
public import FLT.Mazur.SectionGradedLinePullback

/-!
# Actual adjacent boundary tensor-line quotients

The parameter-adic quotient of each boundary tensor power is the original
lower-stage tensor line pushed forward. The quotient projection recovers the
specified section pullback and line comparison in each degree.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve ModuleLineBundleTensorPullback IdealAdicQuotient

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (R : Type) [CommRing R] (m n : ℕ) (h : 2 ≤ n)

/-- The specified system line comparison on the original adjacent transition. -/
def adjacentBoundaryLineIso :
    (pullback (stageRestriction R m n h)).obj (boundaryLine R (m + 1) n h) ≅
      boundaryLine R m n h := by
  simpa only [stageSystem, Functor.ofSequence_map_homOfLE_succ] using
    boundaryLineSystemIso R n h (homOfLE (Nat.le_succ m))

/-- The actual adjacent tensor comparison in every degree. -/
def adjacentBoundaryTensorIso (d : ℕ) :
    (pullback (stageRestriction R m n h)).obj
      (tensorPower (boundaryLine R (m + 1) n h) d) ≅
        tensorPower (boundaryLine R m n h) d :=
  tensorPowerIso (stageRestriction R m n h) (boundaryLine R (m + 1) n h) d ≪≫
    tensorPowerCongr (adjacentBoundaryLineIso R m n h) d

/-- The quotient of the actual upper tensor line is the pushed-forward lower tensor line. -/
def boundaryTensorQuotientIso (d : ℕ) :
    quotient (stageParameterIdeal R (m + 1) n h)
      (tensorPower (boundaryLine R (m + 1) n h) d) (m + 1) ≅
    (pushforward (stageRestriction R m n h)).obj (tensorPower (boundaryLine R m n h) d) :=
  stageLineQuotientIso R m n h _ ((boundaryLine_rankOne R (m + 1) n h).tensorPower d) ≪≫
    (pushforward (stageRestriction R m n h)).mapIso (adjacentBoundaryTensorIso R m n h d)

/-- The quotient projection is the original specified tensor-degree section pullback. -/
@[reassoc] theorem projection_boundaryTensorQuotientIso (d : ℕ) :
    projection (stageParameterIdeal R (m + 1) n h)
      (tensorPower (boundaryLine R (m + 1) n h) d) (m + 1) ≫
      (boundaryTensorQuotientIso R m n h d).hom =
    SectionGradedLinePullback.powerMap (stageRestriction R m n h)
      (adjacentBoundaryLineIso R m n h) d := by
  rw [boundaryTensorQuotientIso, Iso.trans_hom, ← Category.assoc,
    projection_stageLineQuotientIso]
  simp only [adjacentBoundaryTensorIso, Functor.mapIso_hom, Iso.trans_hom, Functor.map_comp,
    SectionGradedLinePullback.powerMap, SectionGradedPullback.powerMap,
    Adjunction.homEquiv_apply, Category.assoc]

end FLT.Mazur.PolygonInfinitesimalStages
