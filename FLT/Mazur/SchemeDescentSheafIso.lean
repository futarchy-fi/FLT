/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeLineDescentCategory
public import FLT.Mazur.SchemeOverlapNormalizationNaturality

/-!
# Transport of geometric descent along a sheaf isomorphism

Conjugating the actual overlap preserves its diagonal and triple cocycle.
This lets a canonical pulled-back line retain a specified geometric model.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.SchemeGeometricDescent
open SchemeOverlapDiagonalChart SchemeTripleOverlap SchemeModulePullbackUnits
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y : Scheme.{u}} (p : Y ⟶ X) {M N : Y.Modules}
  (D : Data p M) (e : M ≅ N)

/-- Conjugate the actual double-overlap map by a specified sheaf comparison. -/
def Data.isoOverlap : Overlap p N :=
  ((pullback (Limits.pullback.fst p p)).mapIso e).symm ≪≫ D.overlap ≪≫
    (pullback (Limits.pullback.snd p p)).mapIso e

/-- The sheaf comparison intertwines the original and transported overlap. -/
theorem Data.isoOverlap_compatible :
    D.overlap.hom ≫ (pullback (Limits.pullback.snd p p)).map e.hom =
      (pullback (Limits.pullback.fst p p)).map e.hom ≫ (D.isoOverlap p e).hom := by
  simp [Data.isoOverlap, ← Functor.map_comp_assoc]

/-- The conjugated overlap retains the actual diagonal equation. -/
theorem Data.isoOverlap_diagonal : Diagonal p N (D.isoOverlap p e) := by
  let d := Limits.pullback.diagonal p
  let l := Limits.pullback.fst p p
  let r := Limits.pullback.snd p p
  have hn (f : Limits.pullback p p ⟶ Y) (hf : d ≫ f = 𝟙 Y) :
      (pullback d).map ((pullback f).map e.hom) ≫ (retractIso d f hf N).hom =
        (retractIso d f hf M).hom ≫ e.hom := by
    exact ((pullbackComp d f ≪≫ pullbackCongr hf ≪≫ pullbackId Y).hom.naturality e.hom)
  change (pullback d).map _ ≫ _ = _
  apply (cancel_epi ((pullback d).map ((pullback l).map e.hom))).mp
  rw [← Category.assoc, ← Functor.map_comp, ← D.isoOverlap_compatible p e,
    Functor.map_comp, Category.assoc, hn r, ← Category.assoc, D.diagonal, hn l]

/-- The conjugated overlap retains the actual triple-overlap cocycle. -/
theorem Data.isoOverlap_cocycle : Cocycle p N (D.isoOverlap p e) := by
  have hn (k : triple p ⟶ Limits.pullback p p) (a b : triple p ⟶ Y)
      (ha : k ≫ Limits.pullback.fst p p = a)
      (hb : k ≫ Limits.pullback.snd p p = b) :=
    normalize_compatible _ _ k a b ha hb D.overlap (D.isoOverlap p e) e.hom
      (D.isoOverlap_compatible p e)
  change (_ ≫ _) = _
  apply (cancel_epi ((pullback (coord1 p)).map e.hom)).mp
  rw [← Category.assoc, ← hn (pair12 p) _ _ rfl rfl,
    Category.assoc, ← hn (pair23 p) _ _ (pair23_fst p) rfl,
    ← Category.assoc, D.cocycle, hn (pair13 p) _ _ (pair13_fst p) (pair13_snd p)]

/-- Actual descent data on the specified isomorphic sheaf, with proved coherence. -/
def Data.ofIso : Data p N where
  overlap := D.isoOverlap p e
  diagonal := D.isoOverlap_diagonal p e
  cocycle := D.isoOverlap_cocycle p e

/-- The specified comparison is a compatible map of actual geometric descent data. -/
theorem Data.ofIso_compatible : D.MapCompatible p (D.ofIso p e) e.hom :=
  D.isoOverlap_compatible p e

end FLT.Mazur.SchemeGeometricDescent
