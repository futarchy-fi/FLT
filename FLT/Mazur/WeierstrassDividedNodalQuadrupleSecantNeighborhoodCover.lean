/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalQuadrupleSecantNeighborhood
public import FLT.Mazur.WeierstrassDividedNodalQuadrupleSecantCoverage

/-!
# Common smooth output neighborhoods cover quadruple-depth secant points

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
  nodalBranchCommonOutput nodalNegativeBranchOutput
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [IsNoetherianRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {k : ℕ} (D : SplitNodeDepth W π (4 * k))
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "s" => π ^ k
local notation "T" => DividedSecantRing W s d.b3 d.b4 d.b6 a c
local notation "j" => IsScalarTower.toAlgHom R S T
local notation "t" => Spec.map (CommRingCat.ofHom (algebraMap S T))
local notation "U" =>
  (finiteGlobalStructure D.uniformizer_ne_zero
    (splitNodeDoubledFamily D) (k + k) le_rfl).smoothLocus

/-- The actual common neighborhoods cover every classified original secant point. -/
theorem nodalQuadrupleSecantNeighborhood_covers
    (hk : 0 < k) (p : PrimeSpectrum T)
    (hp : algebraMap R T π ∈ p.asIdeal)
    (ha : ((j).comp a) (verticalDerivative W s d.b3 d.b4 d.b6) ∉ p.asIdeal)
    (hc : ((j).comp c) (verticalDerivative W s d.b3 d.b4 d.b6) ∉ p.asIdeal) :
    p ∈ finiteReindexedSmoothSecantOpen d a c ∨
      ∃ i : Bool, p ∈ Set.range
        (nodalQuadrupleSecantNeighborhoodInclusion D d a c i) := by
  rcases nodalQuadrupleSecant_smooth_output_cover D d a c
    hk p hp ha hc with hs | hn | hb
  · exact Or.inl hs
  · obtain ⟨q, hq, _, hsm⟩ := hn
    exact Or.inr ⟨true, secantBranchNeighborhood_covers t
      (nodalQuadrupleSecantBranchInclusion D d a c true)
      (nodalQuadrupleSecantBranchOutput D d a c true) U p q hq hsm⟩
  · obtain ⟨q, hq, _, hsm⟩ := hb
    exact Or.inr ⟨false, secantBranchNeighborhood_covers t
      (nodalQuadrupleSecantBranchInclusion D d a c false)
      (nodalQuadrupleSecantBranchOutput D d a c false) U p q hq hsm⟩

/-- The union is an actual open of the original secant, before gluing its outputs. -/
def nodalQuadrupleSecantOutputOpen : (Spec (.of T)).Opens :=
  finiteReindexedSmoothSecantOpen d a c ⊔
    ⨆ i : Bool,
      (nodalQuadrupleSecantNeighborhoodInclusion D d a c i).opensRange

/-- All nodal secants with vertical-smooth inputs lie in the constructed output union. -/
theorem nodalQuadrupleSecantOutputOpen_mem
    (hk : 0 < k) (p : PrimeSpectrum T)
    (hp : algebraMap R T π ∈ p.asIdeal)
    (ha : ((j).comp a) (verticalDerivative W s d.b3 d.b4 d.b6) ∉ p.asIdeal)
    (hc : ((j).comp c) (verticalDerivative W s d.b3 d.b4 d.b6) ∉ p.asIdeal) :
    p ∈ nodalQuadrupleSecantOutputOpen D d a c := by
  rcases nodalQuadrupleSecantNeighborhood_covers D d a c
    hk p hp ha hc with hs | ⟨i, hi⟩
  · exact (show finiteReindexedSmoothSecantOpen d a c ≤
      nodalQuadrupleSecantOutputOpen D d a c from le_sup_left) hs
  · apply (show (⨆ i : Bool,
      (nodalQuadrupleSecantNeighborhoodInclusion D d a c i).opensRange) ≤
        nodalQuadrupleSecantOutputOpen D d a c from le_sup_right)
    exact (le_iSup (fun i =>
      (nodalQuadrupleSecantNeighborhoodInclusion D d a c i).opensRange)
      i) hi

end FLT.Mazur.WeierstrassDividedDepth
