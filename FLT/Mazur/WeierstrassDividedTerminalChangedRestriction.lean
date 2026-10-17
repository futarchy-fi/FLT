/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalChangedSmoothing
public import FLT.Mazur.WeierstrassDividedClosingTransportRestriction
public import FLT.Mazur.PolygonSmoothingChangeParameterNaturality

/-!
# Original quotient maps on the changed terminal chart

The revised smoothing and its whole-chart isomorphism follow the explicit
coefficient restrictions. Both complete residual closing boundaries do too.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => fun k ↦ Quotient R π k
local notation "τ" => fun k ↦ arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π k
local notation "σ" => fun k ↦ arithmeticTerminalChangedSmoothing data H k j hj u hu
local notation "a" => fun k ↦ arithmeticTerminalTangentScale data H k j hj u hu
local notation "N" => fun k ↦ arithmeticTerminalChangedIso data H k j hj u hu
local notation "ρ" => closingOverlapRestriction (R := R) (π := π) m
local notation "F" => closingNormalizedRestriction data H m
local notation "M" => fun k ↦ arithmeticClosingTerminalBoundary data H k j hj u hu
local notation "D" => fun k ↦ arithmeticTerminalChangedBoundary data H k j hj u hu

/-- The revised node uses the original coefficient homomorphism on both coordinates. -/
def arithmeticTerminalChangedRestriction :
    PolygonSmoothing.chart (Q m) (σ m) ⟶ PolygonSmoothing.chart (Q (m + 1)) (σ (m + 1)) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    (arithmeticTerminalChangedSmoothing_restriction data H m j hj u hu hπ)))

local notation "S" => arithmeticTerminalChangedRestriction hπ data H m j hj u hu

/-- The entire changed terminal isomorphism follows the explicit original quotient square. -/
@[reassoc] theorem arithmeticTerminalChangedIso_restriction :
    (N m).hom ≫ S = F ≫ (N (m + 1)).hom := by
  exact changeParameterIso_ringMap (restriction R π m).toRingHom
    (τ (m + 1)) (σ (m + 1)) (τ m) (σ m)
    (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m)
    (arithmeticTerminalChangedSmoothing_restriction data H m j hj u hu hπ)
    (a (m + 1) true) (a (m + 1) false) (a m true) (a m false)
    (congrArg Units.val (arithmeticTerminalTangentScale_restriction data H j hj u hu hπ m true))
    (congrArg Units.val (arithmeticTerminalTangentScale_restriction data H j hj u hu hπ m false))
    rfl rfl

/-- The constructed inverse also preserves the explicit original quotient map. -/
@[reassoc] theorem arithmeticTerminalChangedIso_inv_restriction :
    (N m).inv ≫ F = S ≫ (N (m + 1)).inv := by
  apply (cancel_epi (N m).hom).mp
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, arithmeticTerminalChangedIso_restriction,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Both complete changed boundaries preserve the original overlap coefficient map. -/
@[reassoc] theorem arithmeticTerminalChangedBoundary_restriction (b : Bool) :
    D m b ≫ S = ρ ≫ D (m + 1) b := by
  dsimp only
  rw [← arithmeticTerminalChangedBoundary_transport data H m j hj u hu b, Category.assoc,
    arithmeticTerminalChangedIso_restriction, ← Category.assoc,
    closingTransportTerminal_restriction data H m j hj hπ,
    Category.assoc, arithmeticTerminalChangedBoundary_transport]

/-- The revised full node retains its original coefficient structure under restriction. -/
@[reassoc] theorem arithmeticTerminalChangedRestriction_base :
    S ≫ chartStructure (Q (m + 1)) (σ (m + 1)) =
      chartStructure (Q m) (σ m) ≫ Spec.map (CommRingCat.ofHom (restriction R π m).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext r
  exact ringMap_scalar (restriction R π m).toRingHom (σ (m + 1)) (σ m)
    (arithmeticTerminalChangedSmoothing_restriction data H m j hj u hu hπ) r

end FLT.Mazur.WeierstrassDividedDepth
