/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteNodeAffineCotangentRank
public import FLT.Mazur.PolygonCompleteNodeGenerizationSmooth
public import FLT.Mazur.PrimeCotangentSmoothDimension

/-!
# Relative dimension one near actual generic node generizations

Every original affine prime below a complete node and avoiding the original
parameter has an actual standard-smooth principal neighborhood of relative
dimension one. No relative-dimension assumption on the family is used.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
attribute [local irreducible] originalStageToCompatibleProj

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
  (U : (exactVeroneseProj K n h).affineOpens) (hx : completeNode K n h i ∈ U.1)

/-- An original generic prime below a node has a relative-dimension-one principal neighborhood. -/
theorem completeNodeGenerization_exists_relativeDimension
    (p : Ideal Γ(exactVeroneseProj K n h, U)) [p.IsPrime]
    (hp : p ≤ (U.2.primeIdealOf ⟨completeNode K n h i, hx⟩).asIdeal)
    (ht : completeAffineScalars K n h U PowerSeries.X ∉ p) :
    let _ := (completeAffineScalars K n h U).toAlgebra
    ∃ f : Γ(exactVeroneseProj K n h, U), f ∉ p ∧
      Algebra.IsStandardSmoothOfRelativeDimension 1 (PowerSeries K) (Localization.Away f) := by
  let _ := (completeAffineScalars K n h U).toAlgebra
  let _ := completeAffine_finitePresentation K n h U
  let _ := completeNodeGenerization_isSmoothAt K n h i U hx p hp ht
  exact PrimeCotangentSmoothDimension.exists_notMem_relativeDimension
    (PowerSeries K) Γ(exactVeroneseProj K n h, U) p 1
    (completeNodeAffineDifferentials_finrank K n h i U hx p hp ht)

include U hx in
/-- The actual point form of the principal neighborhood result for a node generization. -/
theorem completeNodeGenerization_point_relativeDimension (y : exactVeroneseProj K n h)
    (hy : y ⤳ completeNode K n h i)
    (ht : PowerSeries.X ∉ ((exactVeroneseProjToBase K n h) y).asIdeal) :
    let hyU := hy.mem_open U.1.isOpen hx
    let p := (U.2.primeIdealOf ⟨y, hyU⟩).asIdeal
    let _ := (completeAffineScalars K n h U).toAlgebra
    ∃ f : Γ(exactVeroneseProj K n h, U), f ∉ p ∧
      Algebra.IsStandardSmoothOfRelativeDimension 1 (PowerSeries K) (Localization.Away f) := by
  apply completeNodeGenerization_exists_relativeDimension K n h i U hx
  · exact AffineStructuralSmoothLocus.primeIdealOf_le_of_specializes U
      ⟨y, hy.mem_open U.1.isOpen hx⟩ ⟨completeNode K n h i, hx⟩ hy
  · exact mt (AffineStructuralSmoothLocus.scalar_mem_primeIdealOf_iff
      (exactVeroneseProjToBase K n h) U ⟨y, hy.mem_open U.1.isOpen hx⟩ PowerSeries.X).mp ht

end FLT.Mazur.PolygonInfinitesimalStages
