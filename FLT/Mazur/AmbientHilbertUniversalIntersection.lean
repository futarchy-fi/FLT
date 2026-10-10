/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmbientHilbertGluedCharts
public import FLT.Mazur.AmbientHilbertUniversalCover
public import FLT.Mazur.RelativeIdealAmbientPullback

/-!
# Actual intersections of universal ambient charts

The ambient above each explicit Hilbert overlap is the full categorical
intersection of the two universal ambient chart embeddings.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.ClosedIdealCover

universe u

namespace FLT.Mazur.HilbertChart.AmbientQuotientCharts

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} {z : Z ⟶ Spec (.of R)}
variable (A : AmbientQuotientCharts R z) (d : ℕ)

/-- The coefficient structure of the concrete ordered Hilbert overlap. -/
abbrev overlapBase (i j : A.Index) : (A.overlap d i j).toScheme ⟶ Spec (.of R) :=
  (A.overlap d i j).ι ≫ A.chartBase d i

/-- The first ambient intersection projection. -/
def universalAmbientOverlapFst (i j : A.Index) :
    pullback (A.overlapBase d i j) z ⟶ pullback (A.chartBase d i) z :=
  relativeIdealAmbientMap z (A.chartBase d i) (A.overlapBase d i j)
    (A.overlap d i j).ι rfl

/-- The second ambient intersection projection, using the actual ordered transition. -/
def universalAmbientOverlapSnd (i j : A.Index) :
    pullback (A.overlapBase d i j) z ⟶ pullback (A.chartBase d j) z :=
  relativeIdealAmbientMap z (A.chartBase d j) (A.overlapBase d i j)
    ((A.transition d i j).hom ≫ (A.overlap d j i).ι)
    ((Category.assoc _ _ _).trans (A.transition_over d i j))

/-- The full ambient over the Hilbert overlap is the actual ambient chart intersection. -/
theorem universalAmbientOverlap_isPullback (i j : A.Index) :
    IsPullback (A.universalAmbientOverlapFst d i j) (A.universalAmbientOverlapSnd d i j)
      (A.universalAmbientChart d i) (A.universalAmbientChart d j) :=
  relativeIdealAmbientMap_square_isPullback z (A.gluedBase d)
    (A.chartBase d i) (A.chartBase d j) (A.overlapBase d i j)
    (A.hilbertChart d i) (A.hilbertChart d j) (A.overlap d i j).ι
    ((A.transition d i j).hom ≫ (A.overlap d j i).ι)
    (A.hilbertChart_over d i) (A.hilbertChart_over d j) rfl
    ((Category.assoc _ _ _).trans (A.transition_over d i j))
    (A.hilbertChart_isPullback d i j)

/-- Identify the explicit overlap ambient with the categorical chart pullback. -/
def universalAmbientOverlapIso (i j : A.Index) :
    pullback (A.overlapBase d i j) z ≅
      pullback (A.universalAmbientChart d i) (A.universalAmbientChart d j) :=
  (A.universalAmbientOverlap_isPullback d i j).isoPullback

end FLT.Mazur.HilbertChart.AmbientQuotientCharts
