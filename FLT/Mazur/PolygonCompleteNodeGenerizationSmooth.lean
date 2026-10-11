/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineStructuralSmoothLocus
public import FLT.Mazur.LocalizedStalkSmoothGenerization
public import FLT.Mazur.PolygonCompleteClosedSmoothLocus
public import FLT.Mazur.PolygonCompleteNodeGenericSmooth

/-!
# Generic generizations of the actual complete nodes are smooth

The punctured original node stalk controls every generization that avoids
the original parameter. This places those actual points in the smooth locus
of the complete structural morphism.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
attribute [local instance] exactVeroneseProjToBase_lfp

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
  (U : (exactVeroneseProj K n h).affineOpens) (hx : completeNode K n h i ∈ U.1)

/-- Affine primes below the actual node and avoiding original q are smooth. -/
theorem completeNodeGenerization_isSmoothAt
    (p : Ideal Γ(exactVeroneseProj K n h, U)) [p.IsPrime]
    (hp : p ≤ (U.2.primeIdealOf ⟨completeNode K n h i, hx⟩).asIdeal)
    (ht : completeAffineScalars K n h U PowerSeries.X ∉ p) :
    let _ := (completeAffineScalars K n h U).toAlgebra
    Algebra.IsSmoothAt (PowerSeries K) p := by
  let L := (exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)
  let q := completeNodeStalkScalars K n h i U hx PowerSeries.X
  let B := Localization.Away q
  let _ := (completeAffineScalars K n h U).toAlgebra
  let _ := TopCat.Presheaf.algebra_section_stalk
    (exactVeroneseProj K n h).presheaf ⟨completeNode K n h i, hx⟩
  let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
  let _ : IsScalarTower (PowerSeries K) Γ(exactVeroneseProj K n h, U) L :=
    IsScalarTower.of_algebraMap_eq' rfl
  let _ := U.2.isLocalization_stalk ⟨completeNode K n h i, hx⟩
  let _ := ((algebraMap L B).comp (completeNodeStalkScalars K n h i U hx)).toAlgebra
  let _ : Module L B := Algebra.toModule
  let _ : Module (PowerSeries K) B := Algebra.toModule
  let _ : SMul L B := Algebra.toSMul
  let _ : SMul (PowerSeries K) B := Algebra.toSMul
  let _ : IsScalarTower (PowerSeries K) L B := IsScalarTower.of_algebraMap_eq' rfl
  let _ := completeNodeGeneric_formallySmooth K n h i U hx
  let _ : IsLocalization.Away
      (algebraMap Γ(exactVeroneseProj K n h, U) L
        (completeAffineScalars K n h U PowerSeries.X)) B := by
    change IsLocalization.Away q B
    infer_instance
  exact LocalizedStalkSmoothGenerization.isSmoothAt (PowerSeries K)
    Γ(exactVeroneseProj K n h, U) L B
    (U.2.primeIdealOf ⟨completeNode K n h i, hx⟩).asIdeal
    (completeAffineScalars K n h U PowerSeries.X) p hp ht

include U hx in
/-- Every generic generization of an actual node lies in the actual family's smooth locus. -/
theorem completeNodeGenerization_mem_smoothLocus (y : exactVeroneseProj K n h)
    (hy : y ⤳ completeNode K n h i)
    (ht : PowerSeries.X ∉ ((exactVeroneseProjToBase K n h) y).asIdeal) :
    y ∈ (exactVeroneseProjToBase K n h).smoothLocus := by
  have hyU : y ∈ U.1 := hy.mem_open U.1.isOpen hx
  apply (AffineStructuralSmoothLocus.mem_smoothLocus_iff
    (exactVeroneseProjToBase K n h) U ⟨y, hyU⟩).mpr
  apply completeNodeGenerization_isSmoothAt K n h i U hx
  · exact AffineStructuralSmoothLocus.primeIdealOf_le_of_specializes U
      ⟨y, hyU⟩ ⟨completeNode K n h i, hx⟩ hy
  · exact mt (AffineStructuralSmoothLocus.scalar_mem_primeIdealOf_iff
      (exactVeroneseProjToBase K n h) U ⟨y, hyU⟩ PowerSeries.X).mp ht

end FLT.Mazur.PolygonInfinitesimalStages
