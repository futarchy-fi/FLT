/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteBoundaryProduct
public import FLT.Mazur.PolygonParameterProductLine

/-!
# The smoothing product on arbitrary boundary parameter schemes

The original closed polygon is retained under arbitrary parameter change.
Restriction of the complete marked line recovers its full boundary product,
and the comparison commutes with the original closed-fiber recovery.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve PolygonParameterTranslation
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completeMarkingDivisor completeBoundaryInclusion
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {T : Scheme} (g : T ⟶ Spec (.of K))
local notation "C" => PolygonCyclicAtlas.polygon K n h
local notation "p" => PolygonCyclicAtlas.normalization K n h
local notation "q" => PolygonCyclicAtlas.nodes K n h
local notation "hn" => (Nat.lt_of_lt_of_le (Nat.succ_pos 1) h)
local notation "hp" => PolygonCyclicPushout.isPushout K n h hn

/-- The original parameter polygon maps to the complete smoothing through its closed fiber. -/
def completeBoundaryParameterMap :
    ((Over.pullback g).obj C).left ⟶ exactVeroneseProj K n h :=
  pullback.fst (C).hom g ≫ completeBoundaryInclusion K n h

/-- The smoothing product recovers the actual original boundary product on every parameter. -/
theorem completeMarkingDivisor_boundaryParameter :
    (completeMarkingDivisor K n h).comap (completeBoundaryParameterMap K n h g) =
      productMarkingIdeal K n p g (fun _ ↦ 1) := by
  rw [completeBoundaryParameterMap, Scheme.IdealSheafData.comap_comp,
    completeMarkingDivisor_boundary, productMarkingIdeal_original]

/-- The complete line recovers the entire product on the original parameter polygon. -/
irreducible_def completeBoundaryParameterLineIso :
    (Scheme.Modules.pullback (completeBoundaryParameterMap K n h g)).obj
      (completeMarkingLine K n h) ≅
        productMarkingLine K n hn p q hp g (fun _ ↦ 1) := by
  let hs := (completeMarkingDivisor_relativeCartier K n h).1
  let ht := (productMarkingIdeal_cartier K n hn p q hp g (fun _ ↦ 1)).1
  let he := completeMarkingDivisor_boundaryParameter K n h g
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  exact divisorLinePullbackIsoOfEq _ hs ht he

/-- Restriction to every original parameter polygon retains the canonical product section. -/
theorem completeBoundaryParameterLineIso_section :
    DivisorLineSectionCompatible (completeBoundaryParameterMap K n h g)
      (completeMarkingDivisor_relativeCartier K n h).1
      (productMarkingIdeal_cartier K n hn p q hp g (fun _ ↦ 1)).1
      (completeBoundaryParameterLineIso K n h g) := by
  let hs := (completeMarkingDivisor_relativeCartier K n h).1
  let ht := (productMarkingIdeal_cartier K n hn p q hp g (fun _ ↦ 1)).1
  let he := completeMarkingDivisor_boundaryParameter K n h g
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  rw [completeBoundaryParameterLineIso_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

/-- Parameter recovery agrees with the original whole closed-boundary comparison. -/
theorem completeBoundaryParameterLineIso_triangle :
    LinePullbackTriangle (pullback.fst (C).hom g) (completeBoundaryInclusion K n h)
      (completeBoundaryParameterMap K n h g) rfl
      (completeBoundaryProductLineIso K n h)
      (productMarkingLineIso K n hn p q hp g (fun _ ↦ 1))
      (completeBoundaryParameterLineIso K n h g) :=
  divisorLineSectionCompatible_triangle _ _ _ _
    (completeBoundaryProductLineIso_section K n h)
    (productMarkingLineIso_section K n hn p q hp g (fun _ ↦ 1))
    (completeBoundaryParameterLineIso_section K n h g)

end FLT.Mazur.PolygonInfinitesimalStages
