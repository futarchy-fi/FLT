/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTripleSecantNeighborhood
public import FLT.Mazur.WeierstrassDividedTripleSecantCoverage

/-!
# Common smooth output neighborhoods cover triple-depth secant points

The three output domains are now actual opens of the original secant
source, with its unchanged inputs. Every nodal point with vertical-smooth
inputs belongs to one of these neighborhoods with an actual smooth output.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
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
local notation "T" => DividedSecantRing W s (d).b3 (d).b4 (d).b6 a c
local notation "j" => IsScalarTower.toAlgHom R S T
local notation "t" => Spec.map (CommRingCat.ofHom (algebraMap S T))
local notation "U" => (finiteGlobalStructure D.uniformizer_ne_zero data k hk).smoothLocus

/-- The actual common neighborhoods cover every classified original secant point. -/
theorem tripleSecantNeighborhood_covers (p : PrimeSpectrum T)
    (hp : algebraMap R T π ∈ p.asIdeal)
    (ha : ((j).comp a) (verticalDerivative W s (d).b3 (d).b4 (d).b6) ∉ p.asIdeal)
    (hc : ((j).comp c) (verticalDerivative W s (d).b3 (d).b4 (d).b6) ∉ p.asIdeal) :
    p ∈ finiteSmoothSecantOpen data k hk a c ∨
      ∃ i : Bool, p ∈ Set.range (tripleSecantNeighborhoodInclusion D data hk a c i) := by
  rcases tripleSecant_smooth_output_cover D data hk a c p hp ha hc with hs | hn | hb
  · exact Or.inl hs
  · obtain ⟨q, hq, _, hsm⟩ := hn
    exact Or.inr ⟨true, secantBranchNeighborhood_covers t
      (tripleSecantBranchInclusion D data hk a c true)
      (tripleSecantBranchOutput D data hk a c true) U p q hq hsm⟩
  · obtain ⟨q, hq, _, hsm⟩ := hb
    exact Or.inr ⟨false, secantBranchNeighborhood_covers t
      (tripleSecantBranchInclusion D data hk a c false)
      (tripleSecantBranchOutput D data hk a c false) U p q hq hsm⟩

/-- The union is an actual open of the original secant, before gluing its outputs. -/
def tripleSecantOutputOpen : (Spec (.of T)).Opens :=
  finiteSmoothSecantOpen data k hk a c ⊔
    ⨆ i : Bool, (tripleSecantNeighborhoodInclusion D data hk a c i).opensRange

/-- All nodal secants with vertical-smooth inputs lie in the constructed output union. -/
theorem tripleSecantOutputOpen_mem (p : PrimeSpectrum T)
    (hp : algebraMap R T π ∈ p.asIdeal)
    (ha : ((j).comp a) (verticalDerivative W s (d).b3 (d).b4 (d).b6) ∉ p.asIdeal)
    (hc : ((j).comp c) (verticalDerivative W s (d).b3 (d).b4 (d).b6) ∉ p.asIdeal) :
    p ∈ tripleSecantOutputOpen D data hk a c := by
  rcases tripleSecantNeighborhood_covers D data hk a c p hp ha hc with hs | ⟨i, hi⟩
  · exact (show finiteSmoothSecantOpen data k hk a c ≤
      tripleSecantOutputOpen D data hk a c from le_sup_left) hs
  · apply (show (⨆ i : Bool,
      (tripleSecantNeighborhoodInclusion D data hk a c i).opensRange) ≤
        tripleSecantOutputOpen D data hk a c from le_sup_right)
    exact (le_iSup (fun i =>
      (tripleSecantNeighborhoodInclusion D data hk a c i).opensRange) i) hi

end FLT.Mazur.WeierstrassDividedDepth
