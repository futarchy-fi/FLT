/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTripleSumDepthMiddleCoverage
public import FLT.Mazur.WeierstrassDividedQuotientResolvedContraction
public import FLT.Mazur.WeierstrassDividedNegativeBranchSource
public import FLT.Mazur.WeierstrassDividedResolvedNegation

/-!
# Negative quotient sum-depth outputs by actual negation

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
  (dd : BranchQuotientData d) (ee : BranchQuotientData e) (h2 : W.a₂ = 0)
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (c : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] S)
local notation "a'" => branchNegativeInput W (π ^ k) d.b3 d.b4 d.b6 a
local notation "c'" => branchNegativeInput W (π ^ l) e.b3 e.b4 e.b6 c

/-- The negative branch uses the actual positive-source construction on negated inputs. -/
def quotientNegativeSumDepthDomain : (Spec (.of S)).Opens :=
  quotientSumDepthDomain hπ d e hkl data hd dd ee h2 a' c'

local notation "O" => quotientNegativeSumDepthDomain hπ d e hkl data hd dd ee h2 a c
variable (j : ℕ) (hj : j ≤ n) (hdj : k + l ≤ j)
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus

/-- Negate the constructed sum of both actual negated inputs in the resolved model. -/
def quotientNegativeSumDepthAddition : (O).toScheme ⟶ (U).toScheme :=
  quotientSumDepthResolvedAddition hπ d e hkl data hd dd ee h2 a' c' j hj hdj ≫
    finiteResolvedNegation hπ data j hj

/-- The negative-branch output retains the original coefficient point. -/
@[reassoc] theorem quotientNegativeSumDepthAddition_structure :
    quotientNegativeSumDepthAddition hπ d e hkl data hd dd ee h2 a c j hj hdj ≫ (U).ι ≫ base =
      (O).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  rw [quotientNegativeSumDepthAddition, Category.assoc, finiteResolvedNegation_structure,
    quotientSumDepthResolvedAddition_structure]
  rfl

local notation "V" => quotientSumDepthSmoothOpen hπ d e hkl data hd dd ee h2 a' c'
local notation "res" => sumDepthSourceRestriction d e a' c' hπ hkl
local notation "c₀" => unequalDepthRight hπ d e hkl c'

/-- On its actual localization the negative construction has the stated cubic contraction. -/
@[reassoc] theorem quotientNegativeSumDepthOutput_contraction :
    quotientSumDepthResolvedOutput hπ d e hkl data hd dd ee h2 a' c' j hj hdj ≫
        finiteResolvedNegation hπ data j hj ≫ (U).ι ≫
          finiteGlobalContraction hπ data j hj =
      (V).ι ≫ Spec.map (CommRingCat.ofHom (res).toRingHom) ≫
        dividedSecantToCurve W (π ^ k) d.b3 d.b4 d.b6 a' c₀
          d.factor3 d.factor4 d.factor6 ≫ WeierstrassIntegralChart.integralCurveNegation W := by
  rw [finiteResolvedNegation_contraction, quotientSumDepthResolvedOutput_contraction_assoc]

end FLT.Mazur.WeierstrassDividedDepth
