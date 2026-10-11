/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierIdealFppfLineGluing
public import FLT.Mazur.SchemeIndependentCanonicalUnitFrames

/-!
# The full ideal inclusion as a compatible descent map

The canonical structure-line frames turn the inclusion of a matching Cartier
ideal into a morphism to canonical descent of the structure sheaf.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open SchemeGeometricDescent SchemeAffineDescent SchemePicard
attribute [local irreducible] ModuleSheafTensor.tensor
variable {X Y : Scheme.{0}} (p : Y ⟶ X) [Flat p]
  (I : Y.IdealSheafData) (hI : EffectiveCartier I)
  (h : I.comap (Limits.pullback.fst p p) = I.comap (Limits.pullback.snd p p))

omit [Flat p] in
/-- The canonical overlap preserves the actual structure-module frames. -/
lemma canonicalStructureOverlap_unit :
    (canonical p (structureModule X)).overlap.hom ≫
        (pullback (Limits.pullback.snd p p)).map (modulePullbackUnitIso p).hom ≫
        (modulePullbackUnitIso (Limits.pullback.snd p p)).hom =
      (pullback (Limits.pullback.fst p p)).map (modulePullbackUnitIso p).hom ≫
        (modulePullbackUnitIso (Limits.pullback.fst p p)).hom :=
  SchemeIndependentCanonicalOverlap.pair_unit p p

/-- The original ideal inclusion is compatible with canonical structure-line descent. -/
lemma cartierIdealInclusion_compatible :
    (cartierIdealDescentData p I hI h).MapCompatible p
      (canonical p (structureModule X))
      (idealModuleι I ≫ (modulePullbackUnitIso p).inv) := by
  unfold Data.MapCompatible
  apply (cancel_mono ((pullback (Limits.pullback.snd p p)).map
    (modulePullbackUnitIso p).hom ≫
      (modulePullbackUnitIso (Limits.pullback.snd p p)).hom)).mp
  simp only [Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [canonicalStructureOverlap_unit]
  simp only [← Functor.map_comp_assoc]
  simpa only [cartierIdealDescentData, idealModulePullbackι,
    Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    cartierIdealDescentOverlap_inclusion p I hI h

/-- The inclusion, with its derived overlap equation, is an actual descent morphism. -/
def cartierIdealInclusionDescentMap :
    cartierIdealLineDatum p I hI h ⟶
      (lineCanonical p).obj ⟨structureModule X, structureModule_locallyFreeRankOne⟩ :=
  ⟨idealModuleι I ≫ (modulePullbackUnitIso p).inv,
    cartierIdealInclusion_compatible p I hI h⟩

end FLT.Mazur.FCurve
