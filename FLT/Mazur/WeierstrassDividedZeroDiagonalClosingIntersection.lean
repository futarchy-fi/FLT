/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroTerminalTransport
public import FLT.Mazur.WeierstrassDividedZeroDiagonalPolygonUnion

/-!
# The actual diagonal closing edges are complete intersections

Transport the original cartesian terminal intersection through every full
chart correction. The normalized equation determines the other boundary
square because the retained chart is an open immersion.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFifthAtlasChart arithmeticZeroFiniteInitialIso arithmeticZeroFiniteLastIso
  arithmeticZeroFiniteTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticZeroDiagonalAtlasChart hπ data H m hj u hu
local notation "D" => arithmeticZeroDiagonalState hπ data H 0 hj u hu

local notation "s" => PolygonArithmeticSimultaneous.State.last D m
local notation "t" => PolygonArithmeticSimultaneous.State.terminal D m
local notation "E" => arithmeticZeroFiniteAtlasIso hπ data H m m hj u hu
local notation "G" => simultaneousTwistedArithmeticIso hπ data H m 0 hj u hu

/-- Both full original diagonal closing intersections are exactly their Laurent spans. -/
theorem arithmeticZeroDiagonalAtlas_closing_isPullback (b : Bool) :
    IsPullback ((edgeInversion Q).hom ≫ leftBranchOpen Q (s b)) (punctureOpen t b)
      (ι (.retained ⟨0, by omega⟩ b)) (ι .terminal) := by
  obtain ⟨e, he⟩ := arithmeticZeroFiniteAtlasIso_terminal_transport
    hπ data H m hj u hu m b
  exact PullbackOneLegTransport.of_right
    (originalClosingAttachment_isPullback hπ data H m 0 hj b) e
    (E (.retained ⟨0, by omega⟩ b)) (E .terminal) G he
    (arithmeticZeroFiniteAtlasIso_chart hπ data H m m hj u hu (.retained ⟨0, by omega⟩ b))
    (arithmeticZeroFiniteAtlasIso_chart hπ data H m m hj u hu .terminal)
    (by simpa only [Category.assoc] using
      arithmeticZeroDiagonalAtlas_closing_normalized hπ data H m hj u hu b)

end FLT.Mazur.WeierstrassDividedDepth
