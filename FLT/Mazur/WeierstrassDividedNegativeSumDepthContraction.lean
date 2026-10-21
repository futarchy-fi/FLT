/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedUnequalNegativeInput
public import FLT.Mazur.WeierstrassDividedNegativeSumDepthOutput

/-!
# Negative sum-depth outputs contract to the original secant

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

/-- The original secant difference is a unit on the negative branch source. -/
theorem negativeSumDepthSource_secantUnit :
    IsUnit ((IsScalarTower.toAlgHom R S B) dx) := by
  simpa only [unequalDepthRight_x, branchNegativeInput_x] using
    sumDepthSource_secantUnit d e a' c' hπ hkl

/-- The original secant algebra restricts to the constructed negative-input source. -/
def negativeSumDepthOriginalRestriction : T →ₐ[R] B :=
  IsLocalization.Away.liftAlgHom (f := IsScalarTower.toAlgHom R S B) dx
    (negativeSumDepthSource_secantUnit hπ d e hkl a c)

/-- Restriction preserves every function of the full original input. -/
theorem negativeSumDepthOriginalRestriction_source (v : S) :
    negativeSumDepthOriginalRestriction hπ d e hkl a c (algebraMap S T v) =
      algebraMap S B v :=
  IsLocalization.Away.lift_eq dx (negativeSumDepthSource_secantUnit hπ d e hkl a c) v

local notation "res" => sumDepthSourceRestriction d e a' c' hπ hkl
local notation "orig" => negativeSumDepthOriginalRestriction hπ d e hkl a c
local notation "old" => dividedSecantToCurve W (π ^ k) d.b3 d.b4 d.b6 a c₀
  d.factor3 d.factor4 d.factor6

/-- On the actual negative source, the negative-input secant negates to the original sum. -/
@[reassoc] theorem negativeSumDepthSource_original :
    Spec.map (CommRingCat.ofHom (res).toRingHom) ≫
        dividedSecantToCurve W (π ^ k) d.b3 d.b4 d.b6 a'
          (unequalDepthRight hπ d e hkl c') d.factor3 d.factor4 d.factor6 ≫
            WeierstrassIntegralChart.integralCurveNegation W =
      Spec.map (CommRingCat.ofHom (orig).toRingHom) ≫ old := by
  apply unequalNegativeSecant_scheme hπ d e hkl c a
  simp only [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext v
  exact (sumDepthSourceRestriction_source d e a' c' hπ hkl v).trans
    (negativeSumDepthOriginalRestriction_source hπ d e hkl a c v).symm

variable [IsBezout R] [IsNoetherianRing R] [Module.Flat R S] {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hd : k + l ≤ n)
  (dd : Data W π (k + k)) (ee : Data W π (l + l)) (h2 : W.a₂ = 0)
  (j : ℕ) (hj : j ≤ n) (hdj : k + l ≤ j)
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "V" => sumDepthSmoothOpen hπ d e hkl data hd dd ee h2 a' c'
local notation "O" => negativeSumDepthDomain hπ d e hkl data hd dd ee h2 a c
local notation "src" => sumDepthSmoothInclusion hπ d e hkl data hd dd ee h2 a' c'

/-- The resolved negative output contracts to the original, unnegated input secant. -/
@[reassoc] theorem negativeSumDepthOutput_original :
    sumDepthResolvedOutput hπ d e hkl data hd dd ee h2 a' c' j hj hdj ≫
        finiteResolvedNegation hπ data j hj ≫ (U).ι ≫
          finiteGlobalContraction hπ data j hj =
      (V).ι ≫ Spec.map (CommRingCat.ofHom (orig).toRingHom) ≫ old := by
  rw [negativeSumDepthOutput_contraction, negativeSumDepthSource_original]

/-- The actual domain maps to the original secant source without changing its inputs. -/
def negativeSumDepthSecantInput : (O).toScheme ⟶ Spec (.of T) :=
  (src).isoOpensRange.inv ≫ (V).ι ≫ Spec.map (CommRingCat.ofHom (orig).toRingHom)

/-- The secant input map retains every point and function of the original source. -/
@[reassoc] theorem negativeSumDepthSecantInput_structure :
    negativeSumDepthSecantInput hπ d e hkl a c data hd dd ee h2 ≫
        Spec.map (CommRingCat.ofHom (algebraMap S T)) = (O).ι := by
  have h : Spec.map (CommRingCat.ofHom (orig).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap S T)) =
        Spec.map (CommRingCat.ofHom (algebraMap S B)) := by
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    ext v
    exact negativeSumDepthOriginalRestriction_source hπ d e hkl a c v
  rw [negativeSumDepthSecantInput, Category.assoc, Category.assoc, h]
  exact Scheme.Hom.isoOpensRange_inv_comp src

/-- Contraction on the original-source domain is precisely the original secant morphism. -/
@[reassoc] theorem negativeSumDepthAddition_original :
    negativeSumDepthAddition hπ d e hkl data hd dd ee h2 a c j hj hdj ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      negativeSumDepthSecantInput hπ d e hkl a c data hd dd ee h2 ≫ old := by
  simp only [negativeSumDepthAddition, sumDepthResolvedAddition, Category.assoc,
    negativeSumDepthOutput_original, negativeSumDepthSecantInput]

end FLT.Mazur.WeierstrassDividedDepth
