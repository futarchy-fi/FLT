/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSumDepthCoverage
public import FLT.Mazur.WeierstrassDividedSumDepthResolvedContraction
public import FLT.Mazur.WeierstrassDividedNegativeBranchSource
public import FLT.Mazur.WeierstrassDividedResolvedNegation

/-!
# Negative-branch sum-depth outputs by actual negation

Apply the positive construction to both negated inputs and negate its
resolved output. This gives an actual open domain and smooth output on
negative punctured branches, with an explicit contracted morphism.
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
  [IsBezout R] [IsNoetherianRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k l n : ℕ}
  (d : Data W π k) (e : Data W π l) (hkl : k ≤ l)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hd : k + l ≤ n)
  (dd : Data W π (k + k)) (ee : Data W π (l + l)) (h2 : W.a₂ = 0)
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (c : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] S)
local notation "a'" => branchNegativeInput W (π ^ k) d.b3 d.b4 d.b6 a
local notation "c'" => branchNegativeInput W (π ^ l) e.b3 e.b4 e.b6 c

/-- The negative branch uses the actual positive-source construction on negated inputs. -/
def negativeSumDepthDomain : (Spec (.of S)).Opens :=
  sumDepthDomain hπ d e hkl data hd dd ee h2 a' c'

local notation "O" => negativeSumDepthDomain hπ d e hkl data hd dd ee h2 a c
variable (j : ℕ) (hj : j ≤ n) (hdj : k + l ≤ j)
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus

/-- Negate the constructed sum of both actual negated inputs in the resolved model. -/
def negativeSumDepthAddition : (O).toScheme ⟶ (U).toScheme :=
  sumDepthResolvedAddition hπ d e hkl data hd dd ee h2 a' c' j hj hdj ≫
    finiteResolvedNegation hπ data j hj

/-- The negative-branch output retains the original coefficient point. -/
@[reassoc] theorem negativeSumDepthAddition_structure :
    negativeSumDepthAddition hπ d e hkl data hd dd ee h2 a c j hj hdj ≫ (U).ι ≫ base =
      (O).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  rw [negativeSumDepthAddition, Category.assoc, finiteResolvedNegation_structure,
    sumDepthResolvedAddition_structure]
  rfl

/-- Negative punctured branches have actual smooth outputs on the unchanged full input spectrum. -/
theorem negativeSumDepthDomain_mem [IsLocalRing R] {m : ℕ}
    (D : SplitNodeDepth W π m) (hk : 0 < k) (hlt : k < l)
    (hm : 2 * (k + l) < m) (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal)
    (hx : a (x W (π ^ k) d.b3 d.b4 d.b6) ∉ p.asIdeal)
    (hu : c (x W (π ^ l) e.b3 e.b4 e.b6) ∉ p.asIdeal)
    (hy : dividedTangentBranchFactor W (π ^ k) d.b3 d.b4 d.b6 a ∈ p.asIdeal)
    (hv : dividedTangentBranchFactor W (π ^ l) e.b3 e.b4 e.b6 c ∈ p.asIdeal) :
    p ∈ O := by
  apply sumDepthDomain_positive_mem D d e hkl data hd dd ee h2 a' c' hk hlt hm p hp
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

local notation "V" => sumDepthSmoothOpen hπ d e hkl data hd dd ee h2 a' c'
local notation "res" => sumDepthSourceRestriction d e a' c' hπ hkl
local notation "c₀" => unequalDepthRight hπ d e hkl c'

/-- On its actual localization the negative construction has the stated cubic contraction. -/
@[reassoc] theorem negativeSumDepthOutput_contraction :
    sumDepthResolvedOutput hπ d e hkl data hd dd ee h2 a' c' j hj hdj ≫
        finiteResolvedNegation hπ data j hj ≫ (U).ι ≫
          finiteGlobalContraction hπ data j hj =
      (V).ι ≫ Spec.map (CommRingCat.ofHom (res).toRingHom) ≫
        dividedSecantToCurve W (π ^ k) d.b3 d.b4 d.b6 a' c₀
          d.factor3 d.factor4 d.factor6 ≫ WeierstrassIntegralChart.integralCurveNegation W := by
  rw [finiteResolvedNegation_contraction, sumDepthResolvedOutput_contraction_assoc]

end FLT.Mazur.WeierstrassDividedDepth
