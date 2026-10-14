/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingCompletedScaling
public import FLT.Mazur.PolygonCompleteNodeCompletion

/-!
# Reciprocal scaling on the actual original node neighborhoods

Conjugating by the constructed original-base comparisons gives automorphisms
of the original full node neighborhoods and completion. This does not identify
them with the contracted cubic action or algebraize them on an open chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
  (U : (exactVeroneseProj K n h).affineOpens) (hx : completeNode K n h i ∈ U.1)
local notation "I" => completeNodeAffineIdeal K n h i U hx
local notation "E" => completeNodeCompletionAlgEquiv K n h i U hx
local notation "e" => completeNodeArithmeticNeighborhoodAlgEquiv K n h i U hx

/-- The original coefficient action on the chosen affine node neighborhood. -/
local instance completeNodeScaleAffineAlgebra :
    Algebra (PowerSeries K) Γ(exactVeroneseProj K n h, U) :=
  (completeAffineScalars K n h U).toAlgebra

/-- Scaling on the actual original node neighborhood, with all ideal powers retained. -/
def completeNodeNeighborhoodScale (a : (PowerSeries K)ˣ) (m : ℕ) :
    (Γ(exactVeroneseProj K n h, U) ⧸ (I) ^ (m + 1)) ≃ₐ[PowerSeries K]
      (Γ(exactVeroneseProj K n h, U) ⧸ (I) ^ (m + 1)) :=
  ((e) m).trans ((nodeScale PowerSeries.X a (m + 1)).trans ((e) m).symm)

/-- The finite original arithmetic comparison intertwines the constructed scaling. -/
theorem completeNodeNeighborhoodScale_comparison (a : (PowerSeries K)ˣ) (m : ℕ)
    (x : Γ(exactVeroneseProj K n h, U) ⧸ (I) ^ (m + 1)) :
    (e) m (completeNodeNeighborhoodScale K n h i U hx a m x) =
      nodeScale PowerSeries.X a (m + 1) ((e) m x) := by
  simp only [completeNodeNeighborhoodScale, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply]

/-- Scaling on the full completion of the actual original affine node. -/
def completeNodeFormalScale (a : (PowerSeries K)ˣ) :
    AdicCompletion (I) Γ(exactVeroneseProj K n h, U) ≃ₐ[PowerSeries K]
      AdicCompletion (I) Γ(exactVeroneseProj K n h, U) :=
  (E).trans ((completedScale PowerSeries.X a).trans (E).symm)

/-- The actual formal comparison intertwines reciprocal scaling. -/
theorem completeNodeFormalScale_comparison (a : (PowerSeries K)ˣ)
    (x : AdicCompletion (I) Γ(exactVeroneseProj K n h, U)) :
    (E) (completeNodeFormalScale K n h i U hx a x) = completedScale PowerSeries.X a ((E) x) := by
  simp only [completeNodeFormalScale, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply]

/-- The actual completion scaling evaluates to the actual original neighborhood scaling. -/
theorem completeNodeFormalScale_eval (a : (PowerSeries K)ˣ) (m : ℕ)
    (x : AdicCompletion (I) Γ(exactVeroneseProj K n h, U)) :
    AdicCompletion.evalₐ (I) (m + 1) (completeNodeFormalScale K n h i U hx a x) =
      completeNodeNeighborhoodScale K n h i U hx a m
        (AdicCompletion.evalₐ (I) (m + 1) x) := by
  apply ((e) m).injective
  rw [completeNodeNeighborhoodScale_comparison]
  change completeNodeArithmeticNeighborhood K n h i U hx m _ = _
  rw [← completeNodeCompletionAlgEquiv_eval, completeNodeFormalScale_comparison,
    completedScale_eval, completeNodeCompletionAlgEquiv_eval]
  rfl

/-- The coefficient unit acts identically on the actual full node completion. -/
@[simp] theorem completeNodeFormalScale_one :
    completeNodeFormalScale K n h i U hx 1 = AlgEquiv.refl := by
  ext x : 1
  apply (E).injective
  rw [completeNodeFormalScale_comparison, completedScale_one]
  rfl

/-- The constructed original completed maps obey multiplication of coefficient units. -/
theorem completeNodeFormalScale_mul (a b : (PowerSeries K)ˣ)
    (x : AdicCompletion (I) Γ(exactVeroneseProj K n h, U)) :
    completeNodeFormalScale K n h i U hx (a * b) x =
      completeNodeFormalScale K n h i U hx a (completeNodeFormalScale K n h i U hx b x) := by
  apply (E).injective
  simp only [completeNodeFormalScale_comparison, completedScale_mul]

/-- Inverting the unit gives the actual inverse original-node automorphism. -/
theorem completeNodeFormalScale_inv (a : (PowerSeries K)ˣ) :
    (completeNodeFormalScale K n h i U hx a).symm =
      completeNodeFormalScale K n h i U hx a⁻¹ := by
  ext x : 1
  apply (completeNodeFormalScale K n h i U hx a).injective
  rw [AlgEquiv.apply_symm_apply, ← completeNodeFormalScale_mul, mul_inv_cancel,
    completeNodeFormalScale_one]
  rfl

end FLT.Mazur.PolygonInfinitesimalStages
