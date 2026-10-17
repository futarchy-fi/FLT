/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteFiniteParameterMarkings
public import FLT.Mazur.PolygonInfinitesimalDivisorLine
public import FLT.Mazur.TensorPowerPullbackSquare

/-!
# Finite scaling and the original parameter marking lines

The original parameter comparison agrees with the actual finite marking-line
comparison, including the canonical sections and all tensor powers.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open CartesianMonoidalCategory
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  tensorPowerPullbackComparison
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "A" => Ring K m
local notation "t" => LaurentPolynomial.C (parameter K m)
local notation "s" => Over.hom (completeFiniteParameterOver K m)
local notation "e" => completeFiniteParameterProductIso K n h m
local notation "u" => PolygonUniversalScaling.u (R := A)
local notation "L₁" => markingLine (A)[T;T⁻¹] (t) n h (fun _ ↦ 1)
local notation "Lᵤ" => markingLine (A)[T;T⁻¹] (t) n h (fun _ ↦ (u))
local notation "c₁" => And.left (markingDivisor_cartier (A)[T;T⁻¹] (t) n h (fun _ ↦ 1))
local notation "cᵤ" => And.left (markingDivisor_cartier (A)[T;T⁻¹] (t) n h (fun _ ↦ (u)))

/-- The finite product identifies the original marking line with the old unit-one line. -/
irreducible_def completeFiniteParameterLineIso :
    (Scheme.Modules.pullback (e).hom).obj (completeFiberMarkingLine K n h (s)) ≅ (L₁) := by
  let hs := (completeFiberMarkingDivisor_relativeCartier K n h (s)).1
  let he := completeFiniteParameterProductIso_ideal K n h m
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ (c₁))
  exact divisorLinePullbackIsoOfEq _ hs (c₁) he

/-- The unit-one line identification preserves the actual canonical marking section. -/
theorem completeFiniteParameterLineIso_section :
    DivisorLineSectionCompatible (e).hom
      (completeFiberMarkingDivisor_relativeCartier K n h (s)).1 (c₁)
      (completeFiniteParameterLineIso K n h m) := by
  let hs := (completeFiberMarkingDivisor_relativeCartier K n h (s)).1
  let he := completeFiniteParameterProductIso_ideal K n h m
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ (c₁))
  rw [completeFiniteParameterLineIso_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

variable (b : ZMod n)
local notation "g" => completeFiniteParameter K n h m b
local notation "f" => completeFiniteScalingRotation K n h m b

/-- The moved original line is the old line at the universal Laurent unit. -/
irreducible_def completeFiniteParameterMovedLineIso :
    (Scheme.Modules.pullback (e).hom).obj (completeParameterMovedLine K n h (g)) ≅ (Lᵤ) := by
  let hs := (completeParameterMovedIdeal_cartier K n h (g)).1
  let he := completeFiniteParameterProductIso_movedIdeal K n h m b
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ (cᵤ))
  exact divisorLinePullbackIsoOfEq _ hs (cᵤ) he

/-- The identification of the moved line preserves the full universal-unit section. -/
theorem completeFiniteParameterMovedLineIso_section :
    DivisorLineSectionCompatible (e).hom
      (completeParameterMovedIdeal_cartier K n h (g)).1 (cᵤ)
      (completeFiniteParameterMovedLineIso K n h m b) := by
  let hs := (completeParameterMovedIdeal_cartier K n h (g)).1
  let he := completeFiniteParameterProductIso_movedIdeal K n h m b
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ (cᵤ))
  rw [completeFiniteParameterMovedLineIso_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

/-- The actual finite scaling pulls the universal-unit ideal to the original unit-one ideal. -/
theorem completeFiniteScalingRotation_ideal :
    (markingDivisor (A)[T;T⁻¹] (t) n h (fun _ ↦ (u))).comap (f) =
      markingDivisor (A)[T;T⁻¹] (t) n h (fun _ ↦ 1) := by
  rw [← completeFiniteParameterProductIso_movedIdeal K n h m b,
    ← Scheme.IdealSheafData.comap_comp, ← completeFiniteParameterTranslation,
    Scheme.IdealSheafData.comap_comp, completeParameterMovedIdeal_pullback]
  change ((completeMarkingDivisor K n h).comap
    (pullback.fst (exactVeroneseProjToBase K n h) (s))).comap (e).hom = _
  rw [completeMarkingDivisor_comap, completeFiniteParameterProductIso_ideal]

/-- The finite map compares the existing positive marking lines themselves. -/
irreducible_def completeFiniteScalingRotationLineIso :
    (Scheme.Modules.pullback (f)).obj (Lᵤ) ≅ (L₁) := by
  let he := completeFiniteScalingRotation_ideal K n h m b
  let _ := idealModulePullbackHom_isIso_of_cartier _ (cᵤ) (he.symm ▸ (c₁))
  exact divisorLinePullbackIsoOfEq _ (cᵤ) (c₁) he

/-- The finite scaling line comparison retains its canonical section. -/
theorem completeFiniteScalingRotationLineIso_section :
    DivisorLineSectionCompatible (f) (cᵤ) (c₁)
      (completeFiniteScalingRotationLineIso K n h m b) := by
  let he := completeFiniteScalingRotation_ideal K n h m b
  let _ := idealModulePullbackHom_isIso_of_cartier _ (cᵤ) (he.symm ▸ (c₁))
  rw [completeFiniteScalingRotationLineIso_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

/-- The original parameter comparison agrees with finite scaling as an actual sheaf square. -/
theorem completeFiniteParameterLineIso_square :
    LinePullbackSquare (e).hom (completeParameterTranslation K n h (g)).left (f) (e).hom
      (completeFiniteParameterTranslation K n h m b)
      (completeParameterOriginalLineIso K n h (g)) (completeFiniteParameterLineIso K n h m)
      (completeFiniteParameterMovedLineIso K n h m b)
      (completeFiniteScalingRotationLineIso K n h m b) :=
  divisorLineSectionCompatible_square _ _ _ _ _
    (completeParameterOriginalLineIso_section K n h (g))
    (completeFiniteParameterLineIso_section K n h m)
    (completeFiniteParameterMovedLineIso_section K n h m b)
    (completeFiniteScalingRotationLineIso_section K n h m b)

/-- Every tensor degree retains the same finite comparison and its equality transport. -/
theorem completeFiniteParameterLineIso_power_square (d : ℕ) :
    LinePullbackSquare (e).hom (completeParameterTranslation K n h (g)).left (f) (e).hom
      (completeFiniteParameterTranslation K n h m b)
      (tensorPowerPullbackComparison _ (completeParameterOriginalLineIso K n h (g)) d)
      (tensorPowerPullbackComparison _ (completeFiniteParameterLineIso K n h m) d)
      (tensorPowerPullbackComparison _ (completeFiniteParameterMovedLineIso K n h m b) d)
      (tensorPowerPullbackComparison _ (completeFiniteScalingRotationLineIso K n h m b) d) :=
  (completeFiniteParameterLineIso_square K n h m b).tensorPower d

end FLT.Mazur.PolygonInfinitesimalStages
