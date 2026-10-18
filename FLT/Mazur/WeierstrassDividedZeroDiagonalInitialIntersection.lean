/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInitialTransport
public import FLT.Mazur.WeierstrassDividedArithmeticLabeledInitialEdge
public import FLT.Mazur.PullbackLeftLegTransport

/-!
# Complete initial intersections in the actual diagonal atlas

The original initial pullback transports through all finite corrections.
Its retained leg keeps the full original Mobius/right substitution.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFifthAtlasChart arithmeticZeroFiniteInitialIso arithmeticZeroFiniteLastIso
  arithmeticZeroFiniteTerminalIso arithmeticZeroFiniteAtlasIso
  simultaneousTwistedArithmeticIso arithmeticInitialBaseEquiv
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticZeroFiniteAtlasChart hπ data H m m hj u hu
local notation "D" => arithmeticZeroFiniteState hπ data H 0 hj u hu m
local notation "s" => PolygonArithmeticSimultaneous.State.last D m
local notation "E" => arithmeticZeroFiniteAtlasIso hπ data H m m hj u hu
local notation "G" => simultaneousTwistedArithmeticIso hπ data H m 0 hj u hu
local notation "P" => arithmeticZeroFiniteInitialPuncture hπ data H m m 0 hj u hu
local notation "B" => punctureSpecIso (arithmeticInitialBaseEquiv data H m 0 hj)

/-- The full original initial intersection retains its actual finite Laurent base. -/
theorem arithmeticZeroDiagonalAtlas_initial_isPullback (b : Bool) :
    IsPullback (P b) ((B).hom ≫ rightBranchOpen Q (s b))
      (ι (.initial b)) (ι (.retained ⟨0, by omega⟩ b)) := by
  obtain ⟨e, he⟩ := arithmeticZeroFiniteAtlasIso_initial_transport
    hπ data H m hj u hu m b
  exact PullbackOneLegTransport.of_left
    (arithmeticLabeledAtlas_initial_edge_isPullback hπ data H m 1 hj (by omega) b)
    e (E (.initial b)) (E (.retained ⟨0, by omega⟩ b)) G he
    (arithmeticZeroFiniteAtlasIso_chart hπ data H m m hj u hu (.initial b))
    (arithmeticZeroFiniteAtlasIso_chart hπ data H m m hj u hu (.retained ⟨0, by omega⟩ b))
    (by simpa only [Category.assoc] using
      arithmeticZeroFiniteAtlas_initial_normalized hπ data H m m hj u hu (by omega) b)

end FLT.Mazur.WeierstrassDividedDepth
