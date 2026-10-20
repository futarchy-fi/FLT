/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalShallowTangentNeighborhood

/-!
# Common smooth neighborhoods cover shallow-depth tangent points

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
  nodalShallowBranchCommonOutput nodalShallowNegativeBranchOutput
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [IsNoetherianRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {n k m : ℕ} (D : SplitNodeDepth W π m)
  (hdepth : 2 * k ≤ m) (hm : m ≤ 3 * k)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hj : m - 2 * k ≤ n)
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "s" => π ^ k
local notation "σ" => nodalSecondShear D k
local notation "a'" => branchNegativeInput W s d.b3 d.b4 d.b6 a
local notation "c'" => branchNegativeInput W s d.b3 d.b4 d.b6 c
local notation "T" => DividedTangentRing W s d.b3 d.b4 d.b6 a c
local notation "t" => Spec.map (CommRingCat.ofHom (algebraMap S T))
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ (start := 0) data (m - 2 * k) hj
local notation "U" => (base).smoothLocus

local notation "dx" => a (x W s d.b3 d.b4 d.b6) - c (x W s d.b3 d.b4 d.b6)

/-- Every nodal tangent point is secant or has an actual common smooth branch output. -/
theorem nodalShallowTangentNeighborhood_covers
    (hlo : 2 * k < m) (hhi : m < 3 * k) (p : PrimeSpectrum T)
    (hp : algebraMap R T π ∈ p.asIdeal) :
    algebraMap S T dx ∉ p.asIdeal ∨
      ∃ i : Bool, p ∈ Set.range
        (nodalShallowTangentNeighborhoodInclusion D hdepth hm data hj d a c i) := by
  let p₀ := PrimeSpectrum.comap (algebraMap S T) p
  have hp₀ : algebraMap R S π ∈ p₀.asIdeal := by
    change algebraMap S T (algebraMap R S π) ∈ p.asIdeal
    rwa [← IsScalarTower.algebraMap_apply]
  have ht : p₀ ∈ PrimeSpectrum.basicOpen (dividedTangentDenominator W s d.b3 d.b4 d.b6 a c) := by
    intro h
    exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem p.asIdeal h
      (IsLocalization.Away.algebraMap_isUnit (S := T) _))
  rcases nodalShallowTangent_smooth_branch_or_secant
    D hdepth hm data hj d a c hlo hhi p₀ hp₀ ht with hs | hn | hb
  · exact Or.inl hs
  · obtain ⟨q, hq, _, hsm⟩ := hn
    exact Or.inr ⟨true, secantBranchNeighborhood_covers t
      (nodalShallowTangentBranchInclusion D d a c true)
      (nodalShallowTangentBranchOutput D hdepth hm data hj d a c true) U p q hq hsm⟩
  · obtain ⟨q, hq, _, hsm⟩ := hb
    exact Or.inr ⟨false, secantBranchNeighborhood_covers t
      (nodalShallowTangentBranchInclusion D d a c false)
      (nodalShallowTangentBranchOutput D hdepth hm data hj d a c false) U p q hq hsm⟩

/-- The actual open union of the two smooth branch neighborhoods. -/
def nodalShallowTangentBranchOutputOpen : (Spec (.of T)).Opens :=
  ⨆ i : Bool,
    (nodalShallowTangentNeighborhoodInclusion D hdepth hm data hj d a c i).opensRange

/-- Nodal tangent points with coincident divided abscissae belong to the output union. -/
theorem nodalShallowTangentBranchOutputOpen_mem
    (hlo : 2 * k < m) (hhi : m < 3 * k) (p : PrimeSpectrum T)
    (hp : algebraMap R T π ∈ p.asIdeal) (hx : algebraMap S T dx ∈ p.asIdeal) :
    p ∈ nodalShallowTangentBranchOutputOpen D hdepth hm data hj d a c := by
  rcases nodalShallowTangentNeighborhood_covers
    D hdepth hm data hj d a c hlo hhi p hp with hs | ⟨i, hi⟩
  · exact (hs hx).elim
  · exact (le_iSup (fun i : Bool =>
      (nodalShallowTangentNeighborhoodInclusion D hdepth hm data hj d a c i).opensRange)
      i) hi

end FLT.Mazur.WeierstrassDividedDepth
