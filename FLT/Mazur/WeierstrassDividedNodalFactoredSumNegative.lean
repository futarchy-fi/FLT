/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalFactoredSumCoverage
public import FLT.Mazur.WeierstrassDividedNegativeBranchSource
public import FLT.Mazur.WeierstrassDividedResolvedNegation

/-!
# Negative factored sum-depth-depth outputs by actual negation

Apply the positive construction to both negated inputs and negate its
resolved output. This gives an actual open domain and smooth output on
negative punctured branches after the constructed finite normalization.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsNoetherianRing R] [IsLocalRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {k l m n : ℕ} (D : SplitNodeDepth W π m)
  (d : Data W π k) (e : Data W π l) (hkl : k ≤ l)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hd : k + l ≤ n)
  (hm : k + 2 * l ≤ m)
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (c : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] S)
local notation "hπ" => D.uniformizer_ne_zero
local notation "a'" => branchNegativeInput W (π ^ k) d.b3 d.b4 d.b6 a
local notation "c'" => branchNegativeInput W (π ^ l) e.b3 e.b4 e.b6 c

/-- The negative branch uses the actual positive-source construction on negated inputs. -/
def nodalFactoredSumNegativeDomain : (Spec (.of S)).Opens :=
  nodalFactoredSumDomain D d e hkl data hd hm a' c'

local notation "O" => nodalFactoredSumNegativeDomain D d e hkl data hd hm a c
variable (j : ℕ) (hj : j ≤ n) (hdj : k + l ≤ j)
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus

/-- Negate the constructed sum of both actual negated inputs in the resolved model. -/
def nodalFactoredSumNegativeAddition : (O).toScheme ⟶ (U).toScheme :=
  nodalFactoredSumResolvedAddition D d e hkl data hd hm a' c' j hj hdj ≫
    finiteResolvedNegation hπ data j hj

/-- The negative-branch output retains the original coefficient point. -/
@[reassoc] theorem nodalFactoredSumNegativeAddition_structure :
    nodalFactoredSumNegativeAddition D d e hkl data hd hm a c j hj hdj ≫ (U).ι ≫ base =
      (O).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  rw [nodalFactoredSumNegativeAddition, Category.assoc, finiteResolvedNegation_structure,
    nodalFactoredSumResolvedAddition_structure]
  rfl

/-- Negative punctured branches have actual smooth outputs on the unchanged full input spectrum. -/
theorem nodalFactoredSumNegativeDomain_mem (hk : 0 < k) (hlt : k < l)
    (hmt : 2 * (k + l) < m) (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal)
    (hx : a (x W (π ^ k) d.b3 d.b4 d.b6) ∉ p.asIdeal)
    (hu : c (x W (π ^ l) e.b3 e.b4 e.b6) ∉ p.asIdeal)
    (hy : dividedTangentBranchFactor W (π ^ k) d.b3 d.b4 d.b6 a ∈ p.asIdeal)
    (hv : dividedTangentBranchFactor W (π ^ l) e.b3 e.b4 e.b6 c ∈ p.asIdeal) :
    p ∈ O := by
  apply nodalFactoredSumDomain_positive_mem D d e hkl data hd hm
    a' c' hk hlt hmt p hp
  · simpa only [branchNegativeInput_x] using hx
  · simpa only [branchNegativeInput_x] using hu
  · have he : a' (y W (π ^ k) d.b3 d.b4 d.b6) =
        -dividedTangentBranchFactor W (π ^ k) d.b3 d.b4 d.b6 a := by
      rw [branchNegativeInput_y, dividedTangentBranchFactor]
      ring
    rw [he]
    exact p.asIdeal.neg_mem hy
  · have he : c' (y W (π ^ l) e.b3 e.b4 e.b6) =
        -dividedTangentBranchFactor W (π ^ l) e.b3 e.b4 e.b6 c := by
      rw [branchNegativeInput_y, dividedTangentBranchFactor]
      ring
    rw [he]
    exact p.asIdeal.neg_mem hv

end FLT.Mazur.WeierstrassDividedDepth
