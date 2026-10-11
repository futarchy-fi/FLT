/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalizedPrimeCotangentRank
public import FLT.Mazur.PolygonCompleteNodeFieldCotangentRank
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Actual affine cotangent ranks below an original complete node

Every affine prime specializing to an original node and avoiding the original
parameter has a one-dimensional cotangent fiber. The field is the residue field
of the original affine prime, and the differentials are those of the original
structural coefficient map.
-/

@[expose] public noncomputable section

open AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
attribute [local irreducible] originalStageToCompatibleProj

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
  (U : (exactVeroneseProj K n h).affineOpens) (hx : completeNode K n h i ∈ U.1)

/-- The original affine differential fiber has rank one below a punctured original node. -/
theorem completeNodeAffineDifferentials_finrank
    (p : Ideal Γ(exactVeroneseProj K n h, U)) [p.IsPrime]
    (hp : p ≤ (U.2.primeIdealOf ⟨completeNode K n h i, hx⟩).asIdeal)
    (ht : completeAffineScalars K n h U PowerSeries.X ∉ p) :
    let A := Γ(exactVeroneseProj K n h, U)
    let _ := (completeAffineScalars K n h U).toAlgebra
    Module.finrank p.ResidueField (p.ResidueField ⊗[A] Ω[A⁄PowerSeries K]) = 1 := by
  let A := Γ(exactVeroneseProj K n h, U)
  let L := (exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)
  let _ := (completeAffineScalars K n h U).toAlgebra
  let _ := TopCat.Presheaf.algebra_section_stalk
    (exactVeroneseProj K n h).presheaf ⟨completeNode K n h i, hx⟩
  let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
  let _ : IsScalarTower (PowerSeries K) A L := IsScalarTower.of_algebraMap_eq' rfl
  let _ := U.2.isLocalization_stalk ⟨completeNode K n h i, hx⟩
  apply LocalizedPrimeCotangentRank.finrank_eq (PowerSeries K) A L
    (U.2.primeIdealOf ⟨completeNode K n h i, hx⟩).asIdeal
    (completeAffineScalars K n h U PowerSeries.X) 1 _ p hp ht
  intro B _ _ htB
  exact completeNodeDifferentials_field_finrank K n h i U hx B htB

end FLT.Mazur.PolygonInfinitesimalStages
