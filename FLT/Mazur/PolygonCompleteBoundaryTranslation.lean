/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteBoundaryParameter
public import FLT.Mazur.PolygonParameterProductMultiplication

/-!
# Complete smoothing recovery on varying translated boundary products

The recovery map includes the inverse of the actual parameter-dependent
translation. Consequently the complete smoothing divisor restricts to the
whole moved product, with its canonical section and original translation triangle.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve PolygonParameterTranslation PolygonUniversalAction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completeMarkingDivisor completeBoundaryParameterMap translationIso
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {T : Scheme} (g : T ⟶ Spec (.of K))
  (c : 𝟙_ (Over T) ⟶ (Over.pullback g).obj (G K n))
local notation "C" => PolygonCyclicAtlas.polygon K n h
local notation "p" => PolygonCyclicAtlas.normalization K n h
local notation "q" => PolygonCyclicAtlas.nodes K n h
local notation "hn" => (Nat.lt_of_lt_of_le (Nat.succ_pos 1) h)
local notation "hp" => PolygonCyclicPushout.isPushout K n h hn
local notation "τ" => translationIso K n hn p q hp g c

/-- The actual moved polygon recovers the original smoothing through inverse translation. -/
def completeMovedBoundaryMap :
    ((Over.pullback g).obj C).left ⟶ exactVeroneseProj K n h :=
  (τ).inv.left ≫ completeBoundaryParameterMap K n h g

/-- The smoothing ideal restricts to the entire moved product, for an arbitrary section. -/
theorem completeMarkingDivisor_movedBoundary :
    (completeMarkingDivisor K n h).comap (completeMovedBoundaryMap K n h g c) =
      movedProductMarkingIdeal K n hn p q hp g c (fun _ ↦ 1) := by
  rw [completeMovedBoundaryMap, Scheme.IdealSheafData.comap_comp,
    completeMarkingDivisor_boundaryParameter, movedProductMarkingIdeal_eq]

/-- Recovery after the forward translation is the original boundary recovery map. -/
theorem translation_completeMovedBoundaryMap :
    (τ).hom.left ≫ completeMovedBoundaryMap K n h g c =
      completeBoundaryParameterMap K n h g := by
  rw [completeMovedBoundaryMap, ← Category.assoc,
    ← Over.comp_left, Iso.hom_inv_id, Over.id_left, Category.id_comp]

/-- The complete smoothing line recovers the full varying boundary product. -/
irreducible_def completeMovedBoundaryLineIso :
    (Scheme.Modules.pullback (completeMovedBoundaryMap K n h g c)).obj
      (completeMarkingLine K n h) ≅
        movedProductMarkingLine K n hn p q hp g c (fun _ ↦ 1) := by
  let hs := (completeMarkingDivisor_relativeCartier K n h).1
  let ht := (movedProductMarkingIdeal_cartier K n hn p q hp g c (fun _ ↦ 1)).1
  let he := completeMarkingDivisor_movedBoundary K n h g c
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  exact divisorLinePullbackIsoOfEq _ hs ht he

/-- The varying recovery preserves the original canonical product-marking section. -/
theorem completeMovedBoundaryLineIso_section :
    DivisorLineSectionCompatible (completeMovedBoundaryMap K n h g c)
      (completeMarkingDivisor_relativeCartier K n h).1
      (movedProductMarkingIdeal_cartier K n hn p q hp g c (fun _ ↦ 1)).1
      (completeMovedBoundaryLineIso K n h g c) := by
  let hs := (completeMarkingDivisor_relativeCartier K n h).1
  let ht := (movedProductMarkingIdeal_cartier K n hn p q hp g c (fun _ ↦ 1)).1
  let he := completeMarkingDivisor_movedBoundary K n h g c
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  rw [completeMovedBoundaryLineIso_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

/-- The smoothing and the actual varying translation give the same whole-product recovery. -/
theorem completeMovedBoundaryLineIso_triangle :
    LinePullbackTriangle (τ).hom.left (completeMovedBoundaryMap K n h g c)
      (completeBoundaryParameterMap K n h g) (translation_completeMovedBoundaryMap K n h g c)
      (completeMovedBoundaryLineIso K n h g c)
      (movedProductMarkingLineIso K n hn p q hp g c (fun _ ↦ 1))
      (completeBoundaryParameterLineIso K n h g) :=
  divisorLineSectionCompatible_triangle _ _ _ _
    (completeMovedBoundaryLineIso_section K n h g c)
    (movedProductMarkingLineIso_section K n hn p q hp g c (fun _ ↦ 1))
    (completeBoundaryParameterLineIso_section K n h g)

end FLT.Mazur.PolygonInfinitesimalStages
