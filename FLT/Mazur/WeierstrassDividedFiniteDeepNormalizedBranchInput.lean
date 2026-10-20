/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteDeepNormalizedBranchLift
public import FLT.Mazur.WeierstrassDividedShearBranchCoverage

/-!
# Construct normalized outputs from the original branch inputs

The shear, coefficient quotient, and transported input maps are constructed
from the original node data. In the supplied finite model the output is smooth
over every original strict-branch special-fiber point when m > 4*k and k > 0.
No second-coefficient normalization of the original equation is assumed.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] rootShearCurve nodalSecondShear nodalSecondQuotient
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {k n m : ℕ} (D : SplitNodeDepth W π m)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hj : k + k ≤ n)
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "r" => nodalSecondShear D k
local notation "V" => rootShearCurve W r
local notation "sd" => shearData d r
local notation "a'" => branchShearInput W (π ^ k) d.b3 d.b4 d.b6 r a
local notation "c'" => branchShearInput W (π ^ k) d.b3 d.b4 d.b6 r c
local notation "B" => DividedTangentBranchRing V (π ^ k) (sd).b3 (sd).b4 (sd).b6 a' c'
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ data (k + k) hj
local notation "old" => dividedTangentDenominator W (π ^ k) d.b3 d.b4 d.b6 a c *
  dividedTangentBranchFactor W (π ^ k) d.b3 d.b4 d.b6 a
local notation "new" => dividedTangentDenominator V (π ^ k) (sd).b3 (sd).b4 (sd).b6 a' c' *
  dividedTangentBranchFactor V (π ^ k) (sd).b3 (sd).b4 (sd).b6 a'

/-- The fully constructed normalized branch output into the original finite model. -/
def deepNodalBranchOutput : Spec (.of B) ⟶ finiteGlobalModel hπ data (k + k) hj :=
  finiteDeepNormalizedBranchLift D data hj d a' c'

/-- The constructed output retains the original coefficient structure. -/
@[reassoc] theorem deepNodalBranchOutput_structure :
    deepNodalBranchOutput D data hj d a c ≫ base = Spec.map (CommRingCat.ofHom (algebraMap R B)) :=
  finiteDeepNormalizedBranchLift_structure D data hj d a' c'

variable [IsNoetherianRing R]

/-- Every special-fiber point of the constructed source has smooth output. -/
theorem deepNodalBranchOutput_smooth (hk : 0 < k) (hm : 4 * k < m)
    (p : PrimeSpectrum B)
    (hp : algebraMap R B π ∈ p.asIdeal) :
    deepNodalBranchOutput D data hj d a c p ∈ (base).smoothLocus :=
  finiteDeepNormalizedBranchLift_nodal_smooth D data hj d a' c' hk hm p hp

/-- Every original strict-branch special-fiber point has a constructed smooth output above it. -/
theorem deepNodalBranchOutput_covers (hk : 0 < k) (hm : 4 * k < m)
    (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal) (hb : p ∈ PrimeSpectrum.basicOpen old) :
    ∃ q : PrimeSpectrum B, PrimeSpectrum.comap (algebraMap S B) q = p ∧
      algebraMap R B π ∈ q.asIdeal ∧
        deepNodalBranchOutput D data hj d a c q ∈ (base).smoothLocus := by
  have hn : p ∈ PrimeSpectrum.basicOpen new :=
    (nodalSecondShear_branch_basicOpen_iff W (π ^ k) d.b3 d.b4 d.b6 a c D k p hp).mpr hb
  have hrange := PrimeSpectrum.localization_away_comap_range B new
  obtain ⟨q, hq⟩ := hrange.ge hn
  have hqπ : algebraMap R B π ∈ q.asIdeal := by
    have h : algebraMap R S π ∈
        (PrimeSpectrum.comap (algebraMap S B) q).asIdeal := hq ▸ hp
    change algebraMap S B (algebraMap R S π) ∈ q.asIdeal at h
    simpa only [IsScalarTower.algebraMap_apply R S B] using h
  exact ⟨q, hq, hqπ, deepNodalBranchOutput_smooth D data hj d a c hk hm q hqπ⟩

end FLT.Mazur.WeierstrassDividedDepth
