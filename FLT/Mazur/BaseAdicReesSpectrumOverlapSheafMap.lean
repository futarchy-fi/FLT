/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesSpectrumOverlap
public import FLT.Mazur.BaseAdicReesSpectrumTransport

/-!
# Actual sheaf comparisons on the full Rees overlap charts

The normalized affine isomorphisms give maps between the pullbacks of the
two fixed sheaves on the full overlap, with their spectrum presentations fixed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (J : Ideal R) [IsLocallyNoetherian X]
  (M : X.Modules) [M.IsFinitePresentation]

attribute [local irreducible] Scheme.Modules.pullback spectrumAffineOverlap spectrumCompositeIso
attribute [local irreducible] AffineIteratedPullbackSections.compositeIso

/-- The two model sheaves on the overlap are compared on a common affine chart. -/
def spectrumOverlapSheafMap {U V W : X.affineOpens} (h : W.1 ≤ U.1) (k : W.1 ≤ V.1) :
    (pullback (spectrumOverlapChart f J h k)).obj
        ((pullback (spectrumOverlapFirst f J U V)).obj
          (spectrumSheaf f J M U)) ⟶
      (pullback (spectrumOverlapChart f J h k)).obj
        ((pullback (spectrumOverlapSecond f J U V)).obj
          (spectrumSheaf f J M V)) :=
  SheafPullbackLocalComparison.transport (spectrumOverlapChart f J h k)
    (spectrumOverlapFirst f J U V) (spectrumOverlapSecond f J U V)
    (spectrumMap f J h) (spectrumMap f J k)
    (spectrumOverlapChart_first f J h k) (spectrumOverlapChart_second f J h k)
    (spectrumSheaf f J M U) (spectrumSheaf f J M V) (spectrumAffineOverlap f J M h k).hom

/-- The transported actual coefficient comparison is invertible. -/
instance spectrumOverlapSheafMap_isIso {U V W : X.affineOpens}
    (h : W.1 ≤ U.1) (k : W.1 ≤ V.1) : IsIso (spectrumOverlapSheafMap f J M h k) := by
  unfold spectrumOverlapSheafMap
  infer_instance

/-- Transport to the full overlap retains the normalized affine comparison. -/
lemma spectrumOverlapSheafMap_normalize {U V W : X.affineOpens}
    (h : W.1 ≤ U.1) (k : W.1 ≤ V.1) :
    spectrumOverlapSheafMap f J M h k ≫
        (SheafPullbackPathComparison.comparison (spectrumOverlapChart f J h k)
          (spectrumOverlapSecond f J U V) (spectrumMap f J k)
          (spectrumOverlapChart_second f J h k)).hom.app (spectrumSheaf f J M V) =
      (SheafPullbackPathComparison.comparison (spectrumOverlapChart f J h k)
          (spectrumOverlapFirst f J U V) (spectrumMap f J h)
          (spectrumOverlapChart_first f J h k)).hom.app (spectrumSheaf f J M U) ≫
        (spectrumAffineOverlap f J M h k).hom :=
  SheafPullbackLocalComparison.transport_normalize _ _ _ _ _ _ _ _ _ _

/-- Local comparisons on the full overlap commute with all further affine refinements. -/
lemma spectrumOverlapSheafMap_refine {U V W Z : X.affineOpens}
    (h : W.1 ≤ U.1) (k : W.1 ≤ V.1) (l : Z.1 ≤ W.1) :
    (pullback (spectrumMap f J l)).map (spectrumOverlapSheafMap f J M h k) ≫
        (AffineIteratedPullbackSections.compositeIso (spectrumMap f J l)
          (spectrumOverlapChart f J h k) (spectrumOverlapChart f J (l.trans h) (l.trans k))
          (spectrumOverlapChart_refine f J h k l)
          ((pullback (spectrumOverlapSecond f J U V)).obj
            (spectrumSheaf f J M V))).hom =
      (AffineIteratedPullbackSections.compositeIso (spectrumMap f J l)
          (spectrumOverlapChart f J h k) (spectrumOverlapChart f J (l.trans h) (l.trans k))
          (spectrumOverlapChart_refine f J h k l)
          ((pullback (spectrumOverlapFirst f J U V)).obj
            (spectrumSheaf f J M U))).hom ≫
        spectrumOverlapSheafMap f J M (l.trans h) (l.trans k) := by
  unfold spectrumOverlapSheafMap
  exact spectrumTransport_refine f J M h k l
    (spectrumOverlapChart f J h k) (spectrumOverlapChart f J (l.trans h) (l.trans k))
    (spectrumOverlapFirst f J U V) (spectrumOverlapSecond f J U V)
    (spectrumOverlapChart_first f J h k) (spectrumOverlapChart_second f J h k)
    (spectrumOverlapChart_refine f J h k l)
    (spectrumOverlapChart_first f J (l.trans h) (l.trans k))
    (spectrumOverlapChart_second f J (l.trans h) (l.trans k))


end FLT.Mazur.BaseAdicRees
