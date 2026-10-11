/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorIdealFunctionalSection
public import FLT.Mazur.PolygonCompletePointCoordinateRange

/-!
# Function numerators on the retained original field square

Every complement function has an actual global tensor-power numerator
with the prescribed ideal-dual restriction. Coordinate representation is
unique whenever that function has a pole bound. Identifying the numerator's
complement coordinate with the starting function is the remaining comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve Scheme.Modules ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] {Y : Scheme}
  (s : Spec (.of L) ⟶ Spec (.of (PowerSeries K)))
  (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h) s)

include hs in
/-- The original retained field square is Noetherian, by its proper structure morphism. -/
theorem completeCartesianPoint_isNoetherian : IsNoetherian Y := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ : IsProper q := MorphismProperty.of_isPullback hs inferInstance
  let _ : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
  let _ : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace q
  exact ⟨⟩

/-- Every original complement function has a numerator in the original divisor tensor powers. -/
theorem completeCartesianPoint_functionNumerator (i : Fin n)
    (a : Γ((completeCartesianPointComplement K n h L s p q hs i).toScheme, ⊤)) :
    let I := (completeCartesianMarking K n h s p q hs i).ker
    let hI := (completeCartesianMarking_relativeCartier K n h s p q hs i).1
    let U := completeCartesianPointComplement K n h L s p q hs i
    ∃ m : ℕ, ∃ t : Γ(tensorPower (divisorLineBundle I hI) m, ⊤),
      (divisorLineBundle (I ^ m) (hI.pow m)).presheaf.map U.leTop.op
        ((divisorLineBundlePowerIso hI m).hom.app ⊤ t) =
      (restrictFunctor U.ι).map (idealModuleι (I ^ m)) ≫
        IdealPowerScalarLift.scalarEnd ((structureModule Y).restrict U.ι) a ≫
          moduleDualUnitSection U 1 := by
  let _ := completeCartesianPoint_isNoetherian K n h L s p q hs
  exact exists_divisorTensorNumerator
    (completeCartesianMarking_relativeCartier K n h s p q hs i).1 a

/-- A finite-pole original function has a unique representing affine coordinate element. -/
theorem completeCartesianPoint_uniqueCoordinateOfPole (i : Fin n) (m : ℕ)
    (a : divisorComplementModule q (completeCartesianMarking K n h s p q hs i).ker)
    (ha : a ∈ divisorPoleSubmodule q
      (completeCartesianMarking_relativeCartier K n h s p q hs i).1 m) :
    ∃! z, completeCartesianPointCoordinateEvaluation K n h L s p q hs i z = a := by
  obtain ⟨z, hz⟩ := completeCartesianPointPole_le_coordinateRange K n h L s p q hs i m ha
  refine ⟨z, hz, fun w hw ↦ ?_⟩
  exact completeCartesianPointCoordinateEvaluation_injective K n h L s p q hs i
    (hw.trans hz.symm)

end FLT.Mazur.PolygonInfinitesimalStages
