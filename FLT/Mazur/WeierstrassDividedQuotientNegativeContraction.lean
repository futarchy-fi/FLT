/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNegativeSumDepthContraction
public import FLT.Mazur.WeierstrassDividedQuotientNegativeOutput

/-!
# Negative quotient outputs contract to the original secant

Restrict the original secant algebra to the actual negative branch source.
Negating the constructed negative-input output then recovers the original
secant as a scheme morphism on the entire constructed domain.
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
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k l : ℕ}
  (d : Data W π k) (e : Data W π l) (hkl : k ≤ l)
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (c : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] S)
local notation "a'" => branchNegativeInput W (π ^ k) d.b3 d.b4 d.b6 a
local notation "c'" => branchNegativeInput W (π ^ l) e.b3 e.b4 e.b6 c
local notation "B" => SumDepthSourceRing d e a' c'
local notation "T" => UnequalDepthSecantRing hπ d e hkl a c
local notation "c₀" => unequalDepthRight hπ d e hkl c
local notation "dx" => a (x W (π ^ k) d.b3 d.b4 d.b6) -
  c₀ (x W (π ^ k) d.b3 d.b4 d.b6)

local notation "res" => sumDepthSourceRestriction d e a' c' hπ hkl
local notation "orig" => negativeSumDepthOriginalRestriction hπ d e hkl a c
local notation "old" => dividedSecantToCurve W (π ^ k) d.b3 d.b4 d.b6 a c₀
  d.factor3 d.factor4 d.factor6

variable [IsBezout R] [IsNoetherianRing R] [Module.Flat R S] {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hd : k + l ≤ n)
  (dd : BranchQuotientData d) (ee : BranchQuotientData e) (h2 : W.a₂ = 0)
  (j : ℕ) (hj : j ≤ n) (hdj : k + l ≤ j)
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "V" => quotientSumDepthSmoothOpen hπ d e hkl data hd dd ee h2 a' c'
local notation "O" => quotientNegativeSumDepthDomain hπ d e hkl data hd dd ee h2 a c
local notation "src" => quotientSumDepthSmoothInclusion hπ d e hkl data hd dd ee h2 a' c'

/-- The resolved negative output contracts to the original, unnegated input secant. -/
@[reassoc] theorem quotientNegativeSumDepthOutput_original :
    quotientSumDepthResolvedOutput hπ d e hkl data hd dd ee h2 a' c' j hj hdj ≫
        finiteResolvedNegation hπ data j hj ≫ (U).ι ≫
          finiteGlobalContraction hπ data j hj =
      (V).ι ≫ Spec.map (CommRingCat.ofHom (orig).toRingHom) ≫ old := by
  rw [quotientNegativeSumDepthOutput_contraction, negativeSumDepthSource_original]

/-- The actual domain maps to the original secant source without changing its inputs. -/
def quotientNegativeSumDepthSecantInput : (O).toScheme ⟶ Spec (.of T) :=
  (src).isoOpensRange.inv ≫ (V).ι ≫ Spec.map (CommRingCat.ofHom (orig).toRingHom)

/-- The secant input map retains every point and function of the original source. -/
@[reassoc] theorem quotientNegativeSumDepthSecantInput_structure :
    quotientNegativeSumDepthSecantInput hπ d e hkl a c data hd dd ee h2 ≫
        Spec.map (CommRingCat.ofHom (algebraMap S T)) = (O).ι := by
  have h : Spec.map (CommRingCat.ofHom (orig).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap S T)) =
        Spec.map (CommRingCat.ofHom (algebraMap S B)) := by
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    ext v
    exact negativeSumDepthOriginalRestriction_source hπ d e hkl a c v
  rw [quotientNegativeSumDepthSecantInput, Category.assoc, Category.assoc, h]
  exact Scheme.Hom.isoOpensRange_inv_comp src

/-- Contraction on the original-source domain is precisely the original secant morphism. -/
@[reassoc] theorem quotientNegativeSumDepthAddition_original :
    quotientNegativeSumDepthAddition hπ d e hkl data hd dd ee h2 a c j hj hdj ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      quotientNegativeSumDepthSecantInput hπ d e hkl a c data hd dd ee h2 ≫ old := by
  simp only [quotientNegativeSumDepthAddition, quotientSumDepthResolvedAddition, Category.assoc,
    quotientNegativeSumDepthOutput_original, quotientNegativeSumDepthSecantInput]

end FLT.Mazur.WeierstrassDividedDepth
