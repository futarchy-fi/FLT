/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicCommonModelFiltration
public import FLT.Mazur.PolygonCompleteNodeFiltration

/-!
# Original node actions on modules over the arithmetic completion

Every arithmetic-completion module receives the actual stalk action.
Its stalk-adic filtration and separation are precisely the arithmetic ones.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open PolygonSmoothing

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj originalStageToCompatibleProj

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
  (U : (exactVeroneseProj K n h).affineOpens) (hx : completeNode K n h i ∈ U.1)
  (N : Type*) [AddCommGroup N]
  [Module (AdicCompletion (coordinateIdeal (PowerSeries.X : PowerSeries K))
    (ChartRing (PowerSeries.X : PowerSeries K))) N]

/-- Restrict the arithmetic completed-ring action through the actual stalk map. -/
@[instance_reducible] def completeNodeArithmeticModule :
    Module ((exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)) N :=
  Module.compHom N (completeNodeArithmeticScalars K n h i U hx)

/-- The transported action is a tower through the arithmetic completed ring. -/
theorem completeNodeArithmeticModule_scalarTower :
    let _ := (completeNodeArithmeticScalars K n h i U hx).toAlgebra
    let _ : Module
      ((exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i))
      (AdicCompletion (coordinateIdeal (PowerSeries.X : PowerSeries K))
        (ChartRing (PowerSeries.X : PowerSeries K))) := Algebra.toModule
    let _ : SMul
      ((exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i))
      (AdicCompletion (coordinateIdeal (PowerSeries.X : PowerSeries K))
        (ChartRing (PowerSeries.X : PowerSeries K))) :=
      ⟨fun a c ↦ completeNodeArithmeticScalars K n h i U hx a * c⟩
    let _ := completeNodeArithmeticModule K n h i U hx N
    IsScalarTower ((exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i))
      (AdicCompletion (coordinateIdeal (PowerSeries.X : PowerSeries K))
        (ChartRing (PowerSeries.X : PowerSeries K))) N := by
  let _ := (completeNodeArithmeticScalars K n h i U hx).toAlgebra
  let _ : Module
    ((exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i))
    (AdicCompletion (coordinateIdeal (PowerSeries.X : PowerSeries K))
      (ChartRing (PowerSeries.X : PowerSeries K))) := Algebra.toModule
  let _ : SMul
    ((exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i))
    (AdicCompletion (coordinateIdeal (PowerSeries.X : PowerSeries K))
      (ChartRing (PowerSeries.X : PowerSeries K))) :=
    ⟨fun a c ↦ completeNodeArithmeticScalars K n h i U hx a * c⟩
  let _ := completeNodeArithmeticModule K n h i U hx N
  exact IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- The transported stalk action retains the original power-series action on every target. -/
theorem completeNodeArithmeticModule_baseScalarTower
    [Module (PowerSeries K) N]
    [IsScalarTower (PowerSeries K)
      (AdicCompletion (coordinateIdeal (PowerSeries.X : PowerSeries K))
        (ChartRing (PowerSeries.X : PowerSeries K))) N] :
    let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
    let _ := completeNodeArithmeticModule K n h i U hx N
    IsScalarTower (PowerSeries K)
      ((exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)) N := by
  let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
  let _ := completeNodeArithmeticModule K n h i U hx N
  apply IsScalarTower.of_algebraMap_smul
  intro r x
  change completeNodeArithmeticScalars K n h i U hx
    (completeNodeStalkScalars K n h i U hx r) • x = r • x
  rw [completeNodeArithmeticScalars_base, algebraMap_smul]

variable [Module (ChartRing (PowerSeries.X : PowerSeries K)) N]
  [IsScalarTower (ChartRing (PowerSeries.X : PowerSeries K))
    (AdicCompletion (coordinateIdeal (PowerSeries.X : PowerSeries K))
      (ChartRing (PowerSeries.X : PowerSeries K))) N]

/-- All module filtration steps agree for the actual original stalk and arithmetic chart. -/
theorem completeNodeArithmeticModule_mem_power_iff (m : ℕ) (x : N) :
    let A := (exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)
    let _ := completeNodeArithmeticModule K n h i U hx N
    x ∈ IsLocalRing.maximalIdeal A ^ m • (⊤ : Submodule A N) ↔
      x ∈ coordinateIdeal (PowerSeries.X : PowerSeries K) ^ m •
        (⊤ : Submodule (ChartRing (PowerSeries.X : PowerSeries K)) N) := by
  let _ := (completeNodeArithmeticScalars K n h i U hx).toAlgebra
  let _ : Module
    ((exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i))
    (AdicCompletion (coordinateIdeal (PowerSeries.X : PowerSeries K))
      (ChartRing (PowerSeries.X : PowerSeries K))) := Algebra.toModule
  let _ : SMul
    ((exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i))
    (AdicCompletion (coordinateIdeal (PowerSeries.X : PowerSeries K))
      (ChartRing (PowerSeries.X : PowerSeries K))) :=
    ⟨fun a c ↦ completeNodeArithmeticScalars K n h i U hx a * c⟩
  let _ := completeNodeArithmeticModule K n h i U hx N
  let _ := completeNodeArithmeticModule_scalarTower K n h i U hx N
  exact AdicCommonModelFiltration.mem_power_iff _ _
    (completeNodeArithmeticScalars_map_maximalIdeal K n h i U hx) m x

/-- Arithmetic separation is separation for the actual original local stalk. -/
theorem completeNodeArithmeticModule_isHausdorff_iff :
    let A := (exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)
    let _ := completeNodeArithmeticModule K n h i U hx N
    IsHausdorff (IsLocalRing.maximalIdeal A) N ↔
      IsHausdorff (coordinateIdeal (PowerSeries.X : PowerSeries K)) N := by
  let _ := (completeNodeArithmeticScalars K n h i U hx).toAlgebra
  let _ : Module
    ((exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i))
    (AdicCompletion (coordinateIdeal (PowerSeries.X : PowerSeries K))
      (ChartRing (PowerSeries.X : PowerSeries K))) := Algebra.toModule
  let _ : SMul
    ((exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i))
    (AdicCompletion (coordinateIdeal (PowerSeries.X : PowerSeries K))
      (ChartRing (PowerSeries.X : PowerSeries K))) :=
    ⟨fun a c ↦ completeNodeArithmeticScalars K n h i U hx a * c⟩
  let _ := completeNodeArithmeticModule K n h i U hx N
  let _ := completeNodeArithmeticModule_scalarTower K n h i U hx N
  exact AdicCommonModelFiltration.isHausdorff_iff _ _
    (completeNodeArithmeticScalars_map_maximalIdeal K n h i U hx)

end FLT.Mazur.PolygonInfinitesimalStages
