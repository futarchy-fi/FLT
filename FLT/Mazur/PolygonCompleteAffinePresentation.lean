/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOriginalAffineScalars
public import FLT.Mazur.PolygonCompleteLineQuotient
public import Mathlib.RingTheory.FinitePresentation

/-!
# Finite presentation of the actual complete affine neighborhoods

Properness of the constructed complete candidate gives finite type for its
actual affine coefficient maps. The original power-series base is
Noetherian, so these maps are finitely presented.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (U : (exactVeroneseProj K n h).affineOpens)

/-- The original coefficient map on every complete affine neighborhood is of finite type. -/
theorem completeAffineScalars_finiteType :
    (completeAffineScalars K n h U).FiniteType := by
  let _ := exactVeroneseProjToBase_isProper K n h
  have hf := (exactVeroneseProjToBase K n h).finiteType_appLE
    (isAffineOpen_top (Spec (.of (PowerSeries K)))) U.2 (by simp)
  exact hf.comp (RingHom.FiniteType.of_surjective
    (Scheme.ΓSpecIso (.of (PowerSeries K))).inv.hom
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (PowerSeries K))).inv).2)

/-- The actual complete affine coefficient map is finitely presented. -/
theorem completeAffineScalars_finitePresentation :
    (completeAffineScalars K n h U).FinitePresentation :=
  RingHom.FinitePresentation.of_finiteType.mp (completeAffineScalars_finiteType K n h U)

/-- In its specified original algebra structure, every actual affine chart is finitely presented. -/
theorem completeAffine_finitePresentation :
    let _ := (completeAffineScalars K n h U).toAlgebra
    Algebra.FinitePresentation (PowerSeries K) Γ(exactVeroneseProj K n h, U) :=
  completeAffineScalars_finitePresentation K n h U

/-- The actual local stalk at every point of the complete candidate is Noetherian. -/
theorem completeStalk_isNoetherian (x : exactVeroneseProj K n h) :
    IsNoetherianRing ((exactVeroneseProj K n h).presheaf.stalk x) :=
  inferInstance

end FLT.Mazur.PolygonInfinitesimalStages
