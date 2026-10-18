/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInitialPunctureAlgebra
public import FLT.Mazur.WeierstrassModificationXArithmeticFactorRatioAlgebra
public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedRetainedSide

/-!
# The full retained attachment for the concrete depth-zero cycle

Construct the algebra equivalence of K inverse followed by the original
base parameter. All accumulated factors remain in the exact Spec equation.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX LaurentPolynomial
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] arithmeticZeroDiagonalState
  arithmeticZeroInitialTotalPunctureEquiv arithmeticZeroFiniteInitialTotalPunctureIso
  arithmeticInitialMobiusEquiv arithmeticFactorRatioLaurentEquiv
variable {R : Type} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m

local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "M" => arithmeticInitialMobiusEquiv π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "L" => arithmeticFactorRatioLaurentEquiv π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "A" => arithmeticZeroInitialTotalPunctureEquiv hπ data H m hj u hu
local notation "K" => arithmeticZeroInfinityNormalizedRetainedParameter hπ data H m hj u hu
local notation "B" => arithmeticInitialBaseEquiv data H m 0 hj

/-- The entire old retained parameter, in contravariant algebra order. -/
def arithmeticZeroRetainedParameterEquiv (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  (L).trans ((M).symm.trans (A b true).symm)

local notation "E" => arithmeticZeroRetainedParameterEquiv hπ data H m hj u hu

/-- The algebra construction gives exactly K, with no coefficient reduction. -/
theorem arithmeticZeroRetainedParameterEquiv_spec (b : Bool) :
    punctureSpecIso (E b) = K b := by
  apply Iso.ext
  simp only [arithmeticZeroRetainedParameterEquiv, punctureSpecIso_trans,
    punctureSpecIso_symm, arithmeticZeroInitialTotalPunctureEquiv_spec,
    arithmeticInitialMobiusEquiv_spec, arithmeticFactorRatioLaurentEquiv_spec,
    arithmeticZeroInfinityNormalizedRetainedParameter, Iso.trans_hom, Iso.symm_hom,
    Category.assoc]

/-- The exact attachment from a normalized initial left branch to the full retained node. -/
def arithmeticZeroRetainedEdgeEquiv (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  (B).trans (E b).symm

/-- The full edge is K inverse followed by the original full base substitution. -/
theorem arithmeticZeroRetainedEdgeEquiv_spec (b : Bool) :
    (punctureSpecIso (arithmeticZeroRetainedEdgeEquiv hπ data H m hj u hu b)).hom =
      (K b).inv ≫ (punctureSpecIso B).hom := by
  rw [arithmeticZeroRetainedEdgeEquiv, punctureSpecIso_trans, punctureSpecIso_symm,
    arithmeticZeroRetainedParameterEquiv_spec]
  rfl

/-- The exact edge reproduces the entire retained-side attachment already in the source. -/
@[reassoc] theorem arithmeticZeroRetainedEdgeEquiv_side (b : Bool) :
    (punctureSpecIso (arithmeticZeroRetainedEdgeEquiv hπ data H m hj u hu b)).hom ≫
      rightBranchOpen Q ((arithmeticZeroDiagonalState hπ data H 0 hj u hu).last m b) =
        arithmeticZeroInfinityNormalizedRetainedSide hπ data H m hj u hu b := by
  simp only [arithmeticZeroInfinityNormalizedRetainedSide,
    arithmeticZeroRetainedEdgeEquiv_spec, Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth
