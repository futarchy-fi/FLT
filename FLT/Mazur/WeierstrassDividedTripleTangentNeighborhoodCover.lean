/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTripleTangentNeighborhood

/-!
# Common smooth neighborhoods cover exact-triple tangent points

The original tangent denominator is invertible on its source. The two
constructed branch neighborhoods therefore cover every nodal point outside
the secant open, without any vertical-derivative restriction on the inputs.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] rootShearCurve nodalSecondShear nodalSecondQuotient
  tripleBranchCommonOutput tripleNegativeBranchOutput
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [IsNoetherianRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {start n k : ℕ}
  (D : SplitNodeDepth W π (3 * (start + k)))
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hk : k ≤ n)
  (a c : Coordinate W (π ^ (start + k))
    (data ⟨k, Nat.lt_succ_of_le hk⟩).b3 (data ⟨k, Nat.lt_succ_of_le hk⟩).b4
    (data ⟨k, Nat.lt_succ_of_le hk⟩).b6 →ₐ[R] S)
local notation "d" => data ⟨k, Nat.lt_succ_of_le hk⟩
local notation "s" => π ^ (start + k)
local notation "σ" => nodalSecondShear D (start + k)
local notation "a'" => branchNegativeInput W s (d).b3 (d).b4 (d).b6 a
local notation "c'" => branchNegativeInput W s (d).b3 (d).b4 (d).b6 c
local notation "T" => DividedTangentRing W s (d).b3 (d).b4 (d).b6 a c
local notation "t" => Spec.map (CommRingCat.ofHom (algebraMap S T))
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "U" => (base).smoothLocus

local notation "dx" => a (x W s (d).b3 (d).b4 (d).b6) - c (x W s (d).b3 (d).b4 (d).b6)

/-- Every nodal tangent point is secant or has an actual common smooth branch output. -/
theorem tripleTangentNeighborhood_covers
    (p : PrimeSpectrum T)
    (hp : algebraMap R T π ∈ p.asIdeal) :
    algebraMap S T dx ∉ p.asIdeal ∨
      ∃ i : Bool, p ∈ Set.range
        (tripleTangentNeighborhoodInclusion D data hk a c i) := by
  let p₀ := PrimeSpectrum.comap (algebraMap S T) p
  have hp₀ : algebraMap R S π ∈ p₀.asIdeal := by
    change algebraMap S T (algebraMap R S π) ∈ p.asIdeal
    rwa [← IsScalarTower.algebraMap_apply]
  have ht : p₀ ∈ PrimeSpectrum.basicOpen
      (dividedTangentDenominator W s (d).b3 (d).b4 (d).b6 a c) := by
    intro h
    exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem p.asIdeal h
      (IsLocalization.Away.algebraMap_isUnit (S := T) _))
  rcases tripleTangent_smooth_branch_or_secant
    D data hk a c p₀ hp₀ ht with hs | hn | hb
  · exact Or.inl hs
  · obtain ⟨q, hq, _, hsm⟩ := hn
    exact Or.inr ⟨true, secantBranchNeighborhood_covers t
      (tripleTangentBranchInclusion D data hk a c true)
      (tripleTangentBranchOutput D data hk a c true) U p q hq hsm⟩
  · obtain ⟨q, hq, _, hsm⟩ := hb
    exact Or.inr ⟨false, secantBranchNeighborhood_covers t
      (tripleTangentBranchInclusion D data hk a c false)
      (tripleTangentBranchOutput D data hk a c false) U p q hq hsm⟩

/-- The actual open union of the two smooth branch neighborhoods. -/
def tripleTangentBranchOutputOpen : (Spec (.of T)).Opens :=
  ⨆ i : Bool,
    (tripleTangentNeighborhoodInclusion D data hk a c i).opensRange

/-- Nodal tangent points with coincident divided abscissae belong to the output union. -/
theorem tripleTangentBranchOutputOpen_mem
    (p : PrimeSpectrum T)
    (hp : algebraMap R T π ∈ p.asIdeal) (hx : algebraMap S T dx ∈ p.asIdeal) :
    p ∈ tripleTangentBranchOutputOpen D data hk a c := by
  rcases tripleTangentNeighborhood_covers
    D data hk a c p hp with hs | ⟨i, hi⟩
  · exact (hs hx).elim
  · exact (le_iSup (fun i : Bool =>
      (tripleTangentNeighborhoodInclusion D data hk a c i).opensRange)
      i) hi

end FLT.Mazur.WeierstrassDividedDepth
