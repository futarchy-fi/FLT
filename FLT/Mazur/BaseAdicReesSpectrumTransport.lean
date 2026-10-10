/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesSpectrumComparison
public import FLT.Mazur.SheafPullbackObjectwiseRefinement

/-!
# Geometric normalization of affine coefficient refinement

The coefficient-composition wrapper equals the geometric chart comparison.
This explicit equality keeps concrete tensor definitions out of subsequent
refinement proofs.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules
open scoped TensorProduct

universe u

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (J : Ideal R) [IsLocallyNoetherian X] (M : X.Modules) [M.IsFinitePresentation]

attribute [local irreducible] Scheme.Modules.pullback
attribute [local irreducible] spectrumMap
attribute [local irreducible] spectrumSheaf
attribute [local irreducible] spectrumAffineOverlap spectrumCompositeIso
attribute [local irreducible] SheafPullbackLocalComparison.transport
attribute [local irreducible] AffineIteratedPullbackSections.compositeIso

/-- Original refinement with geometric comparisons on the fixed spectra. -/
lemma spectrumAffineOverlap_refine_chart {U V W Z : X.affineOpens}
    (i : W.1 ≤ U.1) (j : W.1 ≤ V.1) (k : Z.1 ≤ W.1) :
    (pullback (spectrumMap f J k)).map (spectrumAffineOverlap f J M i j).hom ≫
        (AffineIteratedPullbackSections.compositeIso
          (spectrumMap f J k) (spectrumMap f J j) (spectrumMap f J (k.trans j))
          (spectrumMap_comp f J k j) (spectrumSheaf f J M V)).hom =
      (AffineIteratedPullbackSections.compositeIso
          (spectrumMap f J k) (spectrumMap f J i) (spectrumMap f J (k.trans i))
          (spectrumMap_comp f J k i) (spectrumSheaf f J M U)).hom ≫
        (spectrumAffineOverlap f J M (k.trans i) (k.trans j)).hom := by
  rw [← spectrumCompositeIso_eq, ← spectrumCompositeIso_eq]
  exact spectrumAffineOverlap_refine f J M i j k

variable {O : Scheme.{u}} {U V W Z : X.affineOpens}
variable (i : W.1 ≤ U.1) (j : W.1 ≤ V.1) (k : Z.1 ≤ W.1)

/-- Affine coefficient refinement transports along any compatible geometric chart paths. -/
lemma spectrumTransport_refine
    (c : modelSpectrum f J W ⟶ O) (d : modelSpectrum f J Z ⟶ O)
    (p : O ⟶ modelSpectrum f J U) (q : O ⟶ modelSpectrum f J V)
    (hi : c ≫ p = spectrumMap f J i)
    (hj : c ≫ q = spectrumMap f J j)
    (hd : spectrumMap f J k ≫ c = d)
    (hi' : d ≫ p = spectrumMap f J (k.trans i))
    (hj' : d ≫ q = spectrumMap f J (k.trans j)) :
    (pullback (spectrumMap f J k)).map
        (SheafPullbackLocalComparison.transport c p q
          (spectrumMap f J i) (spectrumMap f J j) hi hj
          (spectrumSheaf f J M U) (spectrumSheaf f J M V)
          (spectrumAffineOverlap f J M i j).hom) ≫
        (AffineIteratedPullbackSections.compositeIso (spectrumMap f J k)
          c d hd ((pullback q).obj (spectrumSheaf f J M V))).hom =
      (AffineIteratedPullbackSections.compositeIso (spectrumMap f J k)
          c d hd ((pullback p).obj (spectrumSheaf f J M U))).hom ≫
        SheafPullbackLocalComparison.transport d p q
          (spectrumMap f J (k.trans i)) (spectrumMap f J (k.trans j))
          hi' hj' (spectrumSheaf f J M U) (spectrumSheaf f J M V)
          (spectrumAffineOverlap f J M (k.trans i) (k.trans j)).hom := by
  exact SheafPullbackLocalComparison.transport_refine_objectwise
    c p q (spectrumMap f J i) (spectrumMap f J j) hi hj
    (spectrumSheaf f J M U) (spectrumSheaf f J M V)
    (spectrumMap f J k) d hd
    (spectrumMap f J (k.trans i)) (spectrumMap f J (k.trans j))
    (spectrumMap_comp f J k i) (spectrumMap_comp f J k j)
    hi' hj' (spectrumAffineOverlap f J M i j).hom
    (spectrumAffineOverlap f J M (k.trans i) (k.trans j)).hom
    (spectrumAffineOverlap_refine_chart f J M i j k)

end FLT.Mazur.BaseAdicRees
