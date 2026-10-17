/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteClosedMovedTranslation

/-!
# The actual inverse complete translation preserves the boundary line comparison

The equality of whole-scheme maps and full marking ideals gives the canonical
line comparison. Section rigidity identifies it with the pre-existing fiber
comparison, including the pullback transport along the proved map equality.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve PolygonParameterTranslation
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completeMarkingDivisor completeFiberMarking
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {T : Scheme} (g : T ⟶ Spec (.of K))
local notation "G" => PolygonSplitGroup.model K n
local notation "P" => PolygonCyclicAtlas.normalization K n h
local notation "Q" => PolygonCyclicAtlas.nodes K n h
local notation "hn" => (Nat.lt_of_lt_of_le (Nat.succ_pos 1) h)
local notation "hp" => PolygonCyclicPushout.isPushout K n h hn
variable (c : 𝟙_ (Over T) ⟶ (Over.pullback g).obj (PolygonSplitGroup.model K n))
local notation "s" => g ≫ completeClosedBase K
local notation "e" => completeUnmovedBoundaryProductIso K n h g
local notation "v" => completeParameterTranslationIso K n h
  (completeClosedParameterSection K n h g c)
local notation "m" => Iso.hom (e) ≫ Over.Hom.left (Iso.inv (v))

/-- The canonical marked-line comparison for the actual complete inverse translation. -/
irreducible_def completeClosedInverseTranslationLineIso :
    (Scheme.Modules.pullback (m)).obj (completeFiberMarkingLine K n h (s)) ≅
      movedProductMarkingLine K n hn P Q hp g c (fun _ ↦ 1) := by
  let hs := (completeFiberMarkingDivisor_relativeCartier K n h (s)).1
  let ht := (movedProductMarkingIdeal_cartier K n hn P Q hp g c (fun _ ↦ 1)).1
  let he := completeClosedInverseTranslation_ideal K n h g c
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  exact divisorLinePullbackIsoOfEq _ hs ht he

/-- The actual complete inverse comparison preserves the canonical full-product section. -/
theorem completeClosedInverseTranslationLineIso_section :
    DivisorLineSectionCompatible (m)
      (completeFiberMarkingDivisor_relativeCartier K n h (s)).1
      (movedProductMarkingIdeal_cartier K n hn P Q hp g c (fun _ ↦ 1)).1
      (completeClosedInverseTranslationLineIso K n h g c) := by
  let hs := (completeFiberMarkingDivisor_relativeCartier K n h (s)).1
  let ht := (movedProductMarkingIdeal_cartier K n hn P Q hp g c (fun _ ↦ 1)).1
  let he := completeClosedInverseTranslation_ideal K n h g c
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  rw [completeClosedInverseTranslationLineIso_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

/-- Section rigidity identifies the actual complete comparison with the original fiber line. -/
theorem completeClosedInverseTranslationLineIso_eq :
    completeClosedInverseTranslationLineIso K n h g c =
      (Scheme.Modules.pullbackCongr
        (completeMovedBoundaryFiberIso_eq_translation K n h g c).symm).app _ ≪≫
          completeBoundaryFiberLineIso K n h g c :=
  (completeClosedInverseTranslationLineIso_section K n h g c).ext
    ((completeBoundaryFiberLineIso_section K n h g c).congr
      (completeMovedBoundaryFiberIso_eq_translation K n h g c).symm)

local notation "d" => Iso.hom (e) ≫ Over.Hom.left (Iso.inv (v)) ≫
  pullback.fst (exactVeroneseProjToBase K n h) (s)

/-- The canonical smoothing-line comparison for the actual inverse complete recovery map. -/
irreducible_def completeClosedInverseRecoveryLineIso :
    (Scheme.Modules.pullback (d)).obj (completeMarkingLine K n h) ≅
      movedProductMarkingLine K n hn P Q hp g c (fun _ ↦ 1) := by
  let hs := (completeMarkingDivisor_relativeCartier K n h).1
  let ht := (movedProductMarkingIdeal_cartier K n hn P Q hp g c (fun _ ↦ 1)).1
  let he : (completeMarkingDivisor K n h).comap (d) =
      movedProductMarkingIdeal K n hn P Q hp g c (fun _ ↦ 1) :=
    completeClosedInverseTranslation_smoothingIdeal K n h g c
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  exact divisorLinePullbackIsoOfEq _ hs ht he

/-- The actual complete inverse recovery preserves the smoothing's canonical marked section. -/
theorem completeClosedInverseRecoveryLineIso_section :
    DivisorLineSectionCompatible (d)
      (completeMarkingDivisor_relativeCartier K n h).1
      (movedProductMarkingIdeal_cartier K n hn P Q hp g c (fun _ ↦ 1)).1
      (completeClosedInverseRecoveryLineIso K n h g c) := by
  let hs := (completeMarkingDivisor_relativeCartier K n h).1
  let ht := (movedProductMarkingIdeal_cartier K n hn P Q hp g c (fun _ ↦ 1)).1
  let he : (completeMarkingDivisor K n h).comap (d) =
      movedProductMarkingIdeal K n hn P Q hp g c (fun _ ↦ 1) :=
    completeClosedInverseTranslation_smoothingIdeal K n h g c
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  rw [completeClosedInverseRecoveryLineIso_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

/-- Section rigidity identifies actual complete recovery with the original moved boundary line. -/
theorem completeClosedInverseRecoveryLineIso_eq :
    completeClosedInverseRecoveryLineIso K n h g c =
      (Scheme.Modules.pullbackCongr
        (completeClosedInverseTranslation_recovery K n h g c)).app _ ≪≫
          completeMovedBoundaryLineIso K n h g c :=
  (completeClosedInverseRecoveryLineIso_section K n h g c).ext
    ((completeMovedBoundaryLineIso_section K n h g c).congr
      (completeClosedInverseTranslation_recovery K n h g c))

end FLT.Mazur.PolygonInfinitesimalStages
