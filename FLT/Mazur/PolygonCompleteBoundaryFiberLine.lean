/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteBoundaryCartesian

/-!
# The original smoothing fiber's line on the translated boundary

The cartesian comparison identifies the complete family's actual fiber marking
with the full moved boundary product. Its positive-line isomorphism retains the
canonical section and agrees with recovery directly from the complete family.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.Obj
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve PolygonParameterTranslation PolygonUniversalAction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completeMarkingDivisor completeFiberMarking
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {T : Scheme} (g : T ⟶ Spec (.of K))
  (c : 𝟙_ (Over T) ⟶ (Over.pullback g).obj (G K n))
local notation "p" => PolygonCyclicAtlas.normalization K n h
local notation "q" => PolygonCyclicAtlas.nodes K n h
local notation "hn" => (Nat.lt_of_lt_of_le (Nat.succ_pos 1) h)
local notation "hp" => PolygonCyclicPushout.isPushout K n h hn
local notation "s" => g ≫ completeClosedBase K
local notation "e" => completeMovedBoundaryFiberIso K n h g c

/-- The original fiber markings pull back to the full varying boundary product itself. -/
theorem completeFiberMarking_movedBoundary :
    (∏ i : Fin n, (completeFiberMarking K n h (s) i).ker).comap (e).hom =
      movedProductMarkingIdeal K n hn p q hp g c (fun _ ↦ 1) := by
  rw [← completeMarkingDivisor_comap, ← Scheme.IdealSheafData.comap_comp,
    completeMovedBoundaryFiberIso_fst, completeMarkingDivisor_movedBoundary]

/-- The fiber's actual marked line recovers the original whole moved product line. -/
irreducible_def completeBoundaryFiberLineIso :
    (Scheme.Modules.pullback (e).hom).obj (completeFiberMarkingLine K n h (s)) ≅
      movedProductMarkingLine K n hn p q hp g c (fun _ ↦ 1) := by
  let hs := (completeFiberMarkingDivisor_relativeCartier K n h (s)).1
  let ht := (movedProductMarkingIdeal_cartier K n hn p q hp g c (fun _ ↦ 1)).1
  let he := completeFiberMarking_movedBoundary K n h g c
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  exact divisorLinePullbackIsoOfEq _ hs ht he

/-- The original fiber comparison preserves the canonical full-product section exactly. -/
theorem completeBoundaryFiberLineIso_section :
    DivisorLineSectionCompatible (e).hom
      (completeFiberMarkingDivisor_relativeCartier K n h (s)).1
      (movedProductMarkingIdeal_cartier K n hn p q hp g c (fun _ ↦ 1)).1
      (completeBoundaryFiberLineIso K n h g c) := by
  let hs := (completeFiberMarkingDivisor_relativeCartier K n h (s)).1
  let ht := (movedProductMarkingIdeal_cartier K n hn p q hp g c (fun _ ↦ 1)).1
  let he := completeFiberMarking_movedBoundary K n h g c
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  rw [completeBoundaryFiberLineIso_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

/-- Actual fiber recovery and direct complete-family recovery agree including the compositor. -/
theorem completeBoundaryFiberLineIso_triangle :
    LinePullbackTriangle (e).hom
      (pullback.fst (exactVeroneseProjToBase K n h) (s))
      (completeMovedBoundaryMap K n h g c) (completeMovedBoundaryFiberIso_fst K n h g c)
      (completeMarkingLineBaseChangeIso K n h (s))
      (completeBoundaryFiberLineIso K n h g c) (completeMovedBoundaryLineIso K n h g c) :=
  divisorLineSectionCompatible_triangle _ _ _ _
    (completeMarkingLineBaseChangeIso_section K n h (s))
    (completeBoundaryFiberLineIso_section K n h g c)
    (completeMovedBoundaryLineIso_section K n h g c)

end FLT.Mazur.PolygonInfinitesimalStages
