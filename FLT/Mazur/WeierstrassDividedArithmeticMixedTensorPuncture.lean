/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticRetainedTerminalAddition
public import FLT.Mazur.WeierstrassDividedRetainedTensorProjection
public import FLT.Mazur.WeierstrassDividedSuccessiveTensorPrimeCoordinates

/-!
# The retained puncture in the full smooth arithmetic mixed pair

The divided formula's first horizontal coordinate is exactly the retained
horizontal tensor coordinate. This compares original arithmetic primes and
retains nilpotents in the coefficient ring.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j ≤ n) (k l : ℕ) (hk : k < j) (hl : l ≤ j)
local notation "a" => retainedOlderFormulaIndex j k hk
local notation "b" => (1 : Fin (j + 3))
local notation "d" => data ⟨k, Nat.lt_succ_of_le (hk.le.trans hj)⟩
local notation "e" => data ⟨l, Nat.lt_succ_of_le (hl.trans hj)⟩
local notation "next" => data ⟨k + 1, Nat.lt_succ_of_le ((Nat.succ_le_iff.mpr hk).trans hj)⟩
local notation "Q" => Quotient R π m
local notation "chart" => arithmeticTensorAtlasMap hπ data m j hj
local notation "s" => finiteGlobalArithmeticStructure hπ data j hj m
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q j hj
local notation "fa" => (O a).ι ≫ chart a ≫ s
local notation "fb" => (O b).ι ≫ chart b ≫ s
local notation "input" => arithmeticRetainedTerminalFormulaInput hπ data m j hj k l hk hl
local notation "I" => (arithmeticRetainedTensorIso hπ data m j hj k hk).inv
local notation "T" => ScalarExtension W (π ^ (0 + k)) π (next).b3 (next).b4 (next).b6 Q
local notation "u" => tensorCoord W (π ^ (0 + k)) π (next).b3 (next).b4 (next).b6 Q 2
local notation "x" => WeierstrassDilatation.x W (π ^ (0 + k)) (d).b3 (d).b4 (d).b6

/-- The entire divided first input factors through the original retained tensor coordinates. -/
@[reassoc] theorem arithmeticMixedFormulaInput_tensor_left :
    input ≫ Spec.map (CommRingCat.ofHom (unequalPairLeft d e).toRingHom) =
      pullback.fst fa fb ≫ (O a).ι ≫ I ≫
        Spec.map (CommRingCat.ofHom (successiveTensorInput hπ d next Q).toRingHom) := by
  rw [arithmeticRetainedTensorIso_contraction,
    arithmeticRetainedTerminalFormulaInput_left]

/-- No puncture is lost when passing from the retained tensor to the mixed formula prime. -/
theorem arithmeticMixedFormulaInput_x_iff (p : (pullback fa fb : Scheme)) :
    unequalPairLeft d e x ∈ (input p).asIdeal ↔
      u ∈ (I ((O a).ι (pullback.fst fa fb p))).asIdeal := by
  have he := congrArg (fun morphism => morphism p)
    (arithmeticMixedFormulaInput_tensor_left hπ data m j hj k l hk hl)
  change PrimeSpectrum.comap (unequalPairLeft d e).toRingHom (input p) =
    PrimeSpectrum.comap (successiveTensorInput hπ d next Q).toRingHom
      (I ((O a).ι (pullback.fst fa fb p))) at he
  change x ∈ (PrimeSpectrum.comap (unequalPairLeft d e).toRingHom (input p)).asIdeal ↔ _
  rw [he, successiveTensorPrime_x]

end FLT.Mazur.WeierstrassDividedDepth
