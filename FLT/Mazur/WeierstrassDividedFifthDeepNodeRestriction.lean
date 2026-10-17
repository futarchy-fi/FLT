/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthDeepGeometry
public import FLT.Mazur.WeierstrassDividedFifthDeepEndRestriction
public import FLT.Mazur.WeierstrassDividedFourthShallowNodeRestriction
public import FLT.Mazur.PolygonArithmeticHigherPunctureIdentification

/-!
# Geometric coefficient squares for every fifth outer-chain factor

Each map is induced by the original arithmetic coefficient quotient on the
complete old or new smoothing. Every full node isomorphism commutes with it.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (m : ℕ)
local notation "s" => arithmeticFifthDeepInput hπ data H j hj u hu
local notation "t" => arithmeticFifthDeepSmoothing hπ data H j hj u hu
local notation "N" => arithmeticFifthDeepNodeIso hπ data H j hj u hu
local notation "τ" => fun k ↦ arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π k
local notation "e" => arithmeticFifthDeepEarlierSmoothing hπ data H j hj u hu
local notation "A" => arithmeticFifthDeepEarlierIso hπ data H j hj u hu

/-- The input node restriction uses its actual fourth smoothing. -/
def arithmeticFifthDeepInputRestriction (v : FifthDeepNode) (b : Bool) :
    PolygonSmoothing.chart (Quotient R π m) (s v m b) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (s v (m + 1) b) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    (arithmeticFifthDeepInput_restriction hπ data H j hj u hu v m b)))

/-- The corrected node restriction includes the full fifth scalar drift. -/
def arithmeticFifthDeepNodeRestriction (v : FifthDeepNode) (b : Bool) :
    PolygonSmoothing.chart (Quotient R π m) (t v m b) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (t v (m + 1) b) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    (arithmeticFifthDeepSmoothing_restriction hπ data H j hj u hu m v b)))

/-- Every paired whole-node isomorphism preserves its two explicit coefficient maps. -/
@[reassoc] theorem arithmeticFifthDeepNodeIso_restriction (v : FifthDeepNode) (b : Bool) :
    arithmeticFifthDeepInputRestriction hπ data H j hj u hu m v b ≫ (N (m + 1) v b).hom =
      (N m v b).hom ≫ arithmeticFifthDeepNodeRestriction hπ data H j hj u hu m v b := by
  exact nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticFifthDeepFactor_restriction hπ data H j hj u hu m v b)

/-- The next earlier corrected node has its own concrete full coefficient restriction. -/
def arithmeticFifthDeepEarlierRestriction (b : Bool) :
    PolygonSmoothing.chart (Quotient R π m) (e m b) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (e (m + 1) b) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    (arithmeticFifthDeepEarlierSmoothing_restriction hπ data H j hj u hu m b)))

/-- The next earlier full factor retains the normalized input and changed output quotients. -/
@[reassoc] theorem arithmeticFifthDeepEarlierIso_restriction (b : Bool) :
    Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom (τ (m + 1)) (τ m)
      (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m))) ≫
        (A (m + 1) b).hom =
      (A m b).hom ≫ arithmeticFifthDeepEarlierRestriction hπ data H j hj u hu m b := by
  exact nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticFifthDeepEarlierFactor_restriction hπ data H j hj u hu m b)

end FLT.Mazur.WeierstrassDividedDepth
