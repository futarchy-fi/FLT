/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticInitialLaurent
public import FLT.Mazur.WeierstrassSuccessiveArithmeticBoundaryCoverage

/-!
# Both initial arithmetic Laurent branches cover the whole original incidence open

The exact original tensor transition transports the full two-branch cover.
The union is precisely D(t) in the original initial arithmetic chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped LaurentPolynomial TensorProduct
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
  (h6 : π ∣ (data ⟨1, Nat.lt_succ_of_le h1⟩).b6)
local notation "β" => WeierstrassSuccessiveX.arithmeticBranchRightBoundary π m W (π ^ start)
  (Data.b3 e) (Data.b4 e) (Data.b6 e) ha hs h2 h3 h4 h6
/-- Every point of the original initial incidence localization lies on a constructed branch. -/
theorem initialArithmeticBoundaries_cover
    (p : Spec (.of (Localization.Away
      ((1 : Q) ⊗ₜ[R] t)))) :
    ∃ (opposite : Bool), ∃ z, (β opposite ≫ (B).hom ≫ (A).inv) z = p := by
  obtain ⟨opposite, z, hx⟩ := WeierstrassSuccessiveX.arithmeticRightBoundaries_cover π m W
    (π ^ start) (Data.b3 e) (Data.b4 e) (Data.b6 e) ha hs h2 h3 h4 h6
    ((B).inv ((A).hom p))
  refine ⟨opposite, z, ?_⟩
  change (A).inv ((B).hom (β opposite z)) = p
  rw [hx]
  have H : (A).hom ≫ (B).inv ≫ (B).hom ≫ (A).inv = 𝟙 _ := by simp
  exact congrArg (fun f ↦ f p) H

/-- The two original initial boundary images together are exactly the full original D(t). -/
theorem initialArithmeticBoundaries_image
    (p : Spec (.of (WeierstrassModificationX.ScalarExtension W (π ^ start)
      (Data.b3 d) (Data.b4 d) (Data.b6 d) Q))) :
    (∃ (opposite : Bool), ∃ z,
      initialArithmeticBranchBoundary hπ data m h1 ha hs h2 h3 h4 h6 opposite z = p) ↔
        ∃ y, PrincipalOpenTensor.inclusion Q t y = p := by
  constructor
  · rintro ⟨opposite, z, hx⟩
    exact ⟨(β opposite ≫ (B).hom ≫ (A).inv) z, hx⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨opposite, z, hx⟩ :=
      initialArithmeticBoundaries_cover hπ data m h1 ha hs h2 h3 h4 h6 y
    refine ⟨opposite, z, ?_⟩
    change PrincipalOpenTensor.inclusion Q t ((β opposite ≫ (B).hom ≫ (A).inv) z) = _
    rw [hx]

end FLT.Mazur.WeierstrassDividedDepth
