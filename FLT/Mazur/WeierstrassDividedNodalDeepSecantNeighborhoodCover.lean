/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalDeepSecantNeighborhood
public import FLT.Mazur.WeierstrassDividedNodalDeepSecantCoverage

/-!
# Common smooth output neighborhoods cover deep-node secant points

The three output domains are now actual opens of the original secant
source, with its unchanged inputs. Every nodal point with vertical-smooth
inputs belongs to one of these neighborhoods with an actual smooth output
when m > 4*k and k > 0.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] rootShearCurve nodalSecondShear nodalSecondQuotient
  deepNodalBranchCommonOutput deepNodalNegativeBranchOutput
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [IsNoetherianRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {k n m : ℕ} (D : SplitNodeDepth W π m)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hj : k + k ≤ n)
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "s" => π ^ k
local notation "T" => DividedSecantRing W s d.b3 d.b4 d.b6 a c
local notation "j" => IsScalarTower.toAlgHom R S T
local notation "t" => Spec.map (CommRingCat.ofHom (algebraMap S T))
local notation "U" =>
  (finiteGlobalStructure D.uniformizer_ne_zero
    data (k + k) hj).smoothLocus

/-- The actual common neighborhoods cover every classified original secant point. -/
theorem nodalDeepSecantNeighborhood_covers
    (hk : 0 < k) (hm : 4 * k < m) (p : PrimeSpectrum T)
    (hp : algebraMap R T π ∈ p.asIdeal)
    (ha : ((j).comp a) (verticalDerivative W s d.b3 d.b4 d.b6) ∉ p.asIdeal)
    (hc : ((j).comp c) (verticalDerivative W s d.b3 d.b4 d.b6) ∉ p.asIdeal) :
    p ∈ finiteReindexedSmoothSecantOpen d a c ∨
      ∃ i : Bool, p ∈ Set.range
        (nodalDeepSecantNeighborhoodInclusion D data hj d a c i) := by
  rcases nodalDeepSecant_smooth_output_cover D data hj d a c
    hk hm p hp ha hc with hs | hn | hb
  · exact Or.inl hs
  · obtain ⟨q, hq, _, hsm⟩ := hn
    exact Or.inr ⟨true, secantBranchNeighborhood_covers t
      (nodalDeepSecantBranchInclusion D d a c true)
      (nodalDeepSecantBranchOutput D data hj d a c true) U p q hq hsm⟩
  · obtain ⟨q, hq, _, hsm⟩ := hb
    exact Or.inr ⟨false, secantBranchNeighborhood_covers t
      (nodalDeepSecantBranchInclusion D d a c false)
      (nodalDeepSecantBranchOutput D data hj d a c false) U p q hq hsm⟩

/-- The union is an actual open of the original secant, before gluing its outputs. -/
def nodalDeepSecantOutputOpen : (Spec (.of T)).Opens :=
  finiteReindexedSmoothSecantOpen d a c ⊔
    ⨆ i : Bool,
      (nodalDeepSecantNeighborhoodInclusion D data hj d a c i).opensRange

/-- All nodal secants with vertical-smooth inputs lie in the constructed output union. -/
theorem nodalDeepSecantOutputOpen_mem
    (hk : 0 < k) (hm : 4 * k < m) (p : PrimeSpectrum T)
    (hp : algebraMap R T π ∈ p.asIdeal)
    (ha : ((j).comp a) (verticalDerivative W s d.b3 d.b4 d.b6) ∉ p.asIdeal)
    (hc : ((j).comp c) (verticalDerivative W s d.b3 d.b4 d.b6) ∉ p.asIdeal) :
    p ∈ nodalDeepSecantOutputOpen D data hj d a c := by
  rcases nodalDeepSecantNeighborhood_covers D data hj d a c
    hk hm p hp ha hc with hs | ⟨i, hi⟩
  · exact (show finiteReindexedSmoothSecantOpen d a c ≤
      nodalDeepSecantOutputOpen D data hj d a c from le_sup_left) hs
  · apply (show (⨆ i : Bool,
      (nodalDeepSecantNeighborhoodInclusion D data hj d a c i).opensRange) ≤
        nodalDeepSecantOutputOpen D data hj d a c from le_sup_right)
    exact (le_iSup (fun i =>
      (nodalDeepSecantNeighborhoodInclusion D data hj d a c i).opensRange)
      i) hi

end FLT.Mazur.WeierstrassDividedDepth
