/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedReflectedCoverage
public import FLT.Mazur.WeierstrassDividedReflectedResolvedContraction
public import FLT.Mazur.WeierstrassDividedNegativeBranchSource
public import FLT.Mazur.WeierstrassDividedResolvedNegation

/-!
# Negative reflected-depth outputs by actual negation

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
  [IsBezout R] [IsNoetherianRing R] [IsLocalRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {k l m n : ℕ} (D : SplitNodeDepth W π m)
  (d : Data W π k) (e : Data W π l) (hkl : k ≤ l)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hd : m - k - l ≤ n)
  (hl : 2 * l ≤ m) (hm : m ≤ k + 2 * l) (h2 : W.a₂ = 0)
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (c : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] S)
local notation "hπ" => D.uniformizer_ne_zero
local notation "a'" => branchNegativeInput W (π ^ k) d.b3 d.b4 d.b6 a
local notation "c'" => branchNegativeInput W (π ^ l) e.b3 e.b4 e.b6 c

/-- The negative branch uses the actual positive-source construction on negated inputs. -/
def reflectedNegativeDomain : (Spec (.of S)).Opens :=
  reflectedDomain D d e hkl data hd hl hm h2 a' c'

local notation "O" => reflectedNegativeDomain D d e hkl data hd hl hm h2 a c
variable (j : ℕ) (hj : j ≤ n) (hdj : m - k - l ≤ j)
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus

/-- Negate the constructed sum of both actual negated inputs in the resolved model. -/
def reflectedNegativeAddition : (O).toScheme ⟶ (U).toScheme :=
  reflectedResolvedAddition D d e hkl data hd hl hm h2 a' c' j hj hdj ≫
    finiteResolvedNegation hπ data j hj

/-- The negative-branch output retains the original coefficient point. -/
@[reassoc] theorem reflectedNegativeAddition_structure :
    reflectedNegativeAddition D d e hkl data hd hl hm h2 a c j hj hdj ≫ (U).ι ≫ base =
      (O).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  rw [reflectedNegativeAddition, Category.assoc, finiteResolvedNegation_structure,
    reflectedResolvedAddition_structure]
  rfl

local notation "V" => reflectedSmoothOpen D d e hkl data hd hl hm h2 a' c'
local notation "res" => sumDepthSourceRestriction d e a' c' hπ hkl
local notation "c₀" => unequalDepthRight hπ d e hkl c'

/-- On its actual localization the negative construction has the stated cubic contraction. -/
@[reassoc] theorem reflectedNegativeOutput_contraction :
    reflectedResolvedOutput D d e hkl data hd hl hm h2 a' c' j hj hdj ≫
        finiteResolvedNegation hπ data j hj ≫ (U).ι ≫
          finiteGlobalContraction hπ data j hj =
      (V).ι ≫ Spec.map (CommRingCat.ofHom (res).toRingHom) ≫
        dividedSecantToCurve W (π ^ k) d.b3 d.b4 d.b6 a' c₀
          d.factor3 d.factor4 d.factor6 ≫ WeierstrassIntegralChart.integralCurveNegation W := by
  rw [finiteResolvedNegation_contraction, reflectedResolvedOutput_contraction_assoc]

end FLT.Mazur.WeierstrassDividedDepth
