/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialTensorSlopeGeometry
public import FLT.Mazur.WeierstrassDividedInitialLaurentParameter
public import FLT.Mazur.WeierstrassDividedArithmeticInitialBranch

/-!
# The original initial arithmetic boundary has its exact Laurent function map

Both constructed labels use the actual initial tensor incidence and the
full nilpotent slope at every arithmetic quotient order.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open PolygonArithmeticStages
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (m : ℕ)
  (h1 : 1 ≤ n)
local notation "Q" => Quotient R π m
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "e" => data (Fin.mk 1 (Nat.lt_succ_of_le h1))
local notation "a" => WeierstrassModificationX.overlapEquiv W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "b" => previousBoundaryEquiv hπ d e
local notation "x" => WeierstrassDilatation.x W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "t" => WeierstrassModificationX.t W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "u" => WeierstrassSuccessiveX.coord W (π ^ start) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) 2
local notation "A" => PrincipalOpenTensor.transitionIso Q x t a
local notation "B" => PrincipalOpenTensor.transitionIso Q x u b

variable (ha : IsUnit W.a₁) (hs : π ∣ π ^ start) (h2 : π ∣ W.a₂)
  (h3 : π ∣ (data ⟨1, Nat.lt_succ_of_le h1⟩).b3)
  (h4 : π ∣ (data ⟨1, Nat.lt_succ_of_le h1⟩).b4)
  (h6 : π ∣ (data ⟨1, Nat.lt_succ_of_le h1⟩).b6) (opposite : Bool)
local notation "c" => WeierstrassSuccessiveX.arithmeticTensorBranchChart π m W (π ^ start)
  (Data.b3 e) (Data.b4 e) (Data.b6 e) ha hs h2 h3 h4 h6 opposite
local notation "β" => WeierstrassSuccessiveX.arithmeticBranchRightBoundary π m W (π ^ start)
  (Data.b3 e) (Data.b4 e) (Data.b6 e) ha hs h2 h3 h4 h6 opposite

local notation "v₁" => WeierstrassSuccessiveX.arithmeticBranchSlope π m W (π ^ start)
  (Data.b3 e) (Data.b4 e) (Data.b6 e) ha hs h2 h3 h4 h6 opposite
local notation "hv₁" => WeierstrassSuccessiveX.arithmeticBranchSlope_equation π m W (π ^ start)
  (Data.b3 e) (Data.b4 e) (Data.b6 e) ha hs h2 h3 h4 h6 opposite

/-- The W329 initial boundary is the actual original full tensor Laurent evaluation. -/
theorem initialArithmeticBranchBoundary_eq_spec :
    initialArithmeticBranchBoundary hπ data m h1 ha hs h2 h3 h4 h6 opposite =
      Spec.map (CommRingCat.ofHom
        (initialTensorSlopeRetraction hπ d e Q v₁ hv₁).toRingHom) := by
  exact (initialTensorSlopeRetraction_spec hπ d e Q v₁ hv₁).symm

/-- The localized W329 boundary has the original inverse-incidence map as a left inverse. -/
@[reassoc] theorem initialArithmeticBoundary_parameter :
    β ≫ (B).hom ≫ (A).inv ≫
      Spec.map (CommRingCat.ofHom (initialTensorLaurentParameter d Q).toRingHom) = 𝟙 _ := by
  change WeierstrassSuccessiveX.tensorSlopeRightBoundary _ _ _ _ _ _ _ _ _ ≫ _ ≫ _ ≫ _ = _
  rw [← initialTensorSlopeLaurent_spec_assoc]
  change Spec.map _ ≫ Spec.map _ = 𝟙 (Spec (.of Q[T;T⁻¹]))
  rw [← Spec.map_comp, ← Spec.map_id]
  exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f.toRingHom))
    (initialTensorLaurentParameter_section hπ d e Q v₁ hv₁)

/-- Each original initial arithmetic boundary is an open chart, including both slope labels. -/
theorem initialArithmeticBranchBoundary_isOpenImmersion :
    IsOpenImmersion
      (initialArithmeticBranchBoundary hπ data m h1 ha hs h2 h3 h4 h6 opposite) := by
  let _ := WeierstrassSuccessiveX.arithmeticTensorBranchChart_isOpenImmersion π m W
    (π ^ start) (Data.b3 e) (Data.b4 e) (Data.b6 e) ha hs h2 h3 h4 h6 opposite
  have H := WeierstrassSuccessiveX.arithmeticBranchRightBoundary_isPullback π m W
    (π ^ start) (Data.b3 e) (Data.b4 e) (Data.b6 e) ha hs h2 h3 h4 h6 opposite
  let _ : IsOpenImmersion β := MorphismProperty.of_isPullback H.flip inferInstance
  unfold initialArithmeticBranchBoundary
  infer_instance

end FLT.Mazur.WeierstrassDividedDepth
