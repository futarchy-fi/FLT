/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSuccessiveTensorCoordinates
public import FLT.Mazur.WeierstrassSuccessiveXArithmeticPuncturedBranches

/-!
# Exact divided input primes of punctured successive tensor charts

The original divided prime has nonzero x and one of its actual two ordinate
branches. These are the input predicates of the constructed addition formulas.
-/

@[expose] public noncomputable section
open AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX PolygonArithmeticStages
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  {k : ℕ} (hπ : π ≠ 0) (d : Data W π k) (e : Data W π (k + 1))
  (S : Type u) [CommRing S] [Algebra R S]
local notation "T" => ScalarExtension W (π ^ k) π e.b3 e.b4 e.b6 S
local notation "u" => tensorCoord W (π ^ k) π e.b3 e.b4 e.b6 S 2
local notation "v" => tensorCoord W (π ^ k) π e.b3 e.b4 e.b6 S 1
local notation "x" => WeierstrassDilatation.x W (π ^ k) d.b3 d.b4 d.b6
local notation "y" => WeierstrassDilatation.y W (π ^ k) d.b3 d.b4 d.b6
local notation "A" => WeierstrassDilatation.Coordinate W (π ^ k) d.b3 d.b4 d.b6
local notation "f" => successiveTensorInput hπ d e S
local notation "q" => fun p => PrimeSpectrum.comap (f).toRingHom p

/-- The divided horizontal puncture is exactly the original tensor horizontal puncture. -/
theorem successiveTensorPrime_x (p : PrimeSpectrum T) :
    x ∈ (q p).asIdeal ↔ u ∈ p.asIdeal := by
  change f x ∈ p.asIdeal ↔ _
  rw [successiveTensorInput_x]

/-- The divided ordinate is the actual tensor product u*v, with no residue substitution. -/
theorem successiveTensorPrime_y (p : PrimeSpectrum T) :
    y ∈ (q p).asIdeal ↔ u * v ∈ p.asIdeal := by
  change f y ∈ p.asIdeal ↔ _
  rw [successiveTensorInput_y]

/-- The opposite divided branch factor is retained exactly under contraction. -/
theorem successiveTensorPrime_negative (p : PrimeSpectrum T) :
    y + algebraMap R A W.a₁ * x ∈ (q p).asIdeal ↔
      u * v + algebraMap R T W.a₁ * u ∈ p.asIdeal := by
  change f (y + algebraMap R A W.a₁ * x) ∈ p.asIdeal ↔ _
  rw [map_add, map_mul, AlgHom.commutes, successiveTensorInput_x, successiveTensorInput_y]

end FLT.Mazur.WeierstrassDividedDepth
