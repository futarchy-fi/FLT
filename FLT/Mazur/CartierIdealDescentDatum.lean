/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierIdealOverlap
public import FLT.Mazur.DivisorLinePullbackIdentity
public import FLT.Mazur.SchemeLineDescentCategory

/-!
# Effective Cartier matching defines honest geometric line descent data

Equality of the two full ideal comaps supplies the canonical line overlap.
Its diagonal and cocycle follow from the actual monic ideal inclusions;
no coherence law is assumed as extra input.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
attribute [local irreducible] ModuleSheafTensor.tensor
open SheafPullbackPathComparison SchemeOverlapDiagonalChart SchemeOverlapCocycleChart
open SchemeGeometricDescent SchemeTripleOverlap SchemeModulePullbackUnits
variable {X Y : Scheme.{0}} (p : Y ⟶ X) [Flat p]
  (I : Y.IdealSheafData) (hI : EffectiveCartier I)
  (h : I.comap (Limits.pullback.fst p p) = I.comap (Limits.pullback.snd p p))

/-- The actual overlap determined by equality of entire Cartier ideals. -/
def cartierIdealDescentOverlap : Overlap p (idealModule I) := by
  letI := idealModulePullbackHom_isIso_of_flat I hI (Limits.pullback.fst p p)
  letI := idealModulePullbackHom_isIso_of_flat I hI (Limits.pullback.snd p p)
  exact cartierIdealOverlapIso I _ _ h

/-- The constructed overlap preserves the original ideal inclusion. -/
lemma cartierIdealDescentOverlap_inclusion :
    (cartierIdealDescentOverlap p I hI h).hom ≫
      idealModulePullbackι I (Limits.pullback.snd p p) =
        idealModulePullbackι I (Limits.pullback.fst p p) := by
  let _ := idealModulePullbackHom_isIso_of_flat I hI (Limits.pullback.fst p p)
  let _ := idealModulePullbackHom_isIso_of_flat I hI (Limits.pullback.snd p p)
  exact cartierIdealOverlapIso_inclusion I _ _ h

attribute [local irreducible] cartierIdealDescentOverlap

/-- The full-ideal overlap has the actual diagonal identity. -/
lemma cartierIdealDescentOverlap_diagonal :
    Diagonal p (idealModule I) (cartierIdealDescentOverlap p I hI h) := by
  let _ := idealModulePullbackHom_isIso_of_flat I hI (Limits.pullback.fst p p)
  let _ := idealModulePullbackHom_isIso_of_flat I hI (Limits.pullback.snd p p)
  let d := Limits.pullback.diagonal p
  let l := Limits.pullback.fst p p
  let r := Limits.pullback.snd p p
  have hi : idealModulePullbackι I (𝟙 Y) =
      (pullbackId Y).hom.app (idealModule I) ≫ idealModuleι I := by
    rw [idealModulePullbackι, modulePullbackUnitIso_id]
    exact (pullbackId Y).hom.naturality (idealModuleι I)
  have he := congrArg (fun m ↦ (pullback d).map m ≫ (modulePullbackUnitIso d).hom)
    (cartierIdealDescentOverlap_inclusion p I hI h)
  rw [Functor.map_comp, Category.assoc,
    idealModulePullbackι_comparison I d r (𝟙 Y) (Limits.pullback.diagonal_snd p),
    idealModulePullbackι_comparison I d l (𝟙 Y) (Limits.pullback.diagonal_fst p), hi] at he
  apply (cancel_mono (idealModuleι I)).mp
  simpa only [Diagonal, DiagonalCompatible, retractIso,
    comparison, Iso.trans_hom, Iso.app_hom, NatTrans.comp_app, Category.assoc] using he

/-- The original full-ideal overlap satisfies the actual triple-overlap cocycle. -/
lemma cartierIdealDescentOverlap_cocycle :
    Cocycle p (idealModule I) (cartierIdealDescentOverlap p I hI h) := by
  let _ := idealModulePullbackHom_isIso_of_flat I hI (Limits.pullback.fst p p)
  let _ := idealModulePullbackHom_isIso_of_flat I hI (Limits.pullback.snd p p)
  let _ := idealModulePullbackHom_isIso_of_flat I hI (coord3 p)
  let _ := idealModulePullbackι_mono I (coord3 p)
  apply (cancel_mono (idealModulePullbackι I (coord3 p))).mp
  have he := cartierIdealDescentOverlap_inclusion p I hI h
  change (_ ≫ _) ≫ _ = _ ≫ _
  rw [Category.assoc, idealOverlap_normalize_inclusion I _ _ (pair23 p) _ _
    (pair23_fst p) rfl _ he,
    idealOverlap_normalize_inclusion I _ _ (pair12 p) _ _ rfl rfl _ he,
    idealOverlap_normalize_inclusion I _ _ (pair13 p) _ _
      (pair13_fst p) (pair13_snd p) _ he]

/-- A matching Cartier ideal determines full geometric descent data for its actual ideal line. -/
def cartierIdealDescentData : Data p (idealModule I) where
  overlap := cartierIdealDescentOverlap p I hI h
  diagonal := cartierIdealDescentOverlap_diagonal p I hI h
  cocycle := cartierIdealDescentOverlap_cocycle p I hI h

/-- The matched full ideal, with its proved rank and coherence, as actual line descent data. -/
def cartierIdealLineDatum : LineData p where
  obj := idealModule I
  rankOne := hI.idealModule_locallyFreeRankOne
  datum := cartierIdealDescentData p I hI h

end FLT.Mazur.FCurve
