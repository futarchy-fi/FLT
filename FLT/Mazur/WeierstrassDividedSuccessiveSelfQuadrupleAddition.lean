/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSuccessiveSelfDeepAddition
public import FLT.Mazur.WeierstrassDividedQuadruplePromotedAddition

/-!
# Equal tensor inputs at exact quadruple node depth

Pull back the genuine quadruple law from the flat integral pair. Its output
retains the final supplied smooth model and covers punctured inputs together
with the reciprocal law, including coincident inputs over arithmetic thickenings.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation WeierstrassSuccessiveX PolygonArithmeticStages
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {k n depth : ℕ}
  (node : SplitNodeDepth W π depth) (d : Data W π k) (e : Data W π (k + 1))
  (S : Type) [CommRing S] [Algebra R S]
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (j : ℕ) (hj : j ≤ n) (hsum : k + k ≤ j) (hquad : depth = 4 * k)
local notation "hπ" => node.uniformizer_ne_zero
local notation "P" => SuccessiveTensorPairRing e e S
local notation "f" => successiveTensorPairInput hπ d e d e S
local notation "input" => Spec.map (CommRingCat.ofHom (f).toRingHom)
local notation "a" => unequalPairLeft d d
local notation "b" => unequalPairRight d d
local notation "N" => (show SplitNodeDepth W π (4 * k) from hquad ▸ node)
local notation "O" => nodalQuadrupleAdditionOpen N d a b
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus

/-- The quadruple output domain in the whole equal-depth tensor pair. -/
def successiveSelfQuadrupleOpen : (Spec (.of P)).Opens := input ⁻¹ᵁ O

local notation "D" => successiveSelfQuadrupleOpen node d e S hquad
local notation "E" => successiveSelfReciprocalOpen node d e S

/-- The quadruple formula has its actual output in the supplied final smooth model. -/
def successiveSelfQuadrupleAddition : (D).toScheme ⟶ (U).toScheme :=
  (input ∣_ O) ≫ quadruplePromotedAddition N data (hsum.trans hj) d a b j hj hsum

/-- The quadruple output preserves the whole original coefficient morphism. -/
@[reassoc] theorem successiveSelfQuadrupleAddition_structure :
    successiveSelfQuadrupleAddition node d e S data j hj hsum hquad ≫ (U).ι ≫ base =
      (D).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R P)) := by
  rw [successiveSelfQuadrupleAddition, Category.assoc, quadruplePromotedAddition_structure,
    morphismRestrict_ι_assoc, successiveTensorPairInput_structure]
  rfl

variable (m : ℕ)
local notation "Q" => Quotient R π m
local notation "T" => SuccessiveTensorPairRing e e Q
local notation "g" => successiveTensorPairInput hπ d e d e Q
local notation "u₁" => successiveTensorPairLeft e e Q
  (tensorCoord W (π ^ k) π e.b3 e.b4 e.b6 Q 2)
local notation "u₂" => successiveTensorPairRight e e Q
  (tensorCoord W (π ^ k) π e.b3 e.b4 e.b6 Q 2)

/-- Both equal-depth punctured arithmetic inputs reach an actual output, even on the diagonal. -/
theorem successiveSelfQuadruple_punctured_cover (hk : 0 < k)
    (p : PrimeSpectrum T) (hx : u₁ ∉ p.asIdeal) (hu : u₂ ∉ p.asIdeal) :
    p ∈ successiveSelfQuadrupleOpen node d e Q hquad ∨
      p ∈ successiveSelfReciprocalOpen node d e Q := by
  let q := PrimeSpectrum.comap (g).toRingHom p
  have hp : algebraMap R (UnequalPairRing d d) π ∈ q.asIdeal := by
    change g (algebraMap R (UnequalPairRing d d) π) ∈ p.asIdeal
    rw [AlgHom.commutes]
    exact arithmeticPrime_parameter_mem π m T p
  have hx' : a (x W (π ^ k) d.b3 d.b4 d.b6) ∉ q.asIdeal := by
    change g (a _) ∉ p.asIdeal
    rwa [successiveTensorPairInput_left_apply, successiveTensorInput_x]
  have hu' : b (x W (π ^ k) d.b3 d.b4 d.b6) ∉ q.asIdeal := by
    change g (b _) ∉ p.asIdeal
    rwa [successiveTensorPairInput_right_apply, successiveTensorInput_x]
  have ha := preMiddleInput_vertical_not_mem node d a hk (by omega) q hp hx'
  have hb := preMiddleInput_vertical_not_mem node d b hk (by omega) q hp hu'
  by_cases hdx : a (x W (π ^ k) d.b3 d.b4 d.b6) -
      b (x W (π ^ k) d.b3 d.b4 d.b6) ∈ q.asIdeal
  · by_cases he : dividedTangentDenominator W (π ^ k) d.b3 d.b4 d.b6 a b ∈ q.asIdeal
    · exact Or.inr (suppliedReciprocalDomain_mem_of_denominators d a b q hdx he ha)
    · exact Or.inl (nodalQuadrupleAdditionOpen_source_tangent N d a b q hp hdx he)
  · exact Or.inl (nodalQuadrupleAdditionOpen_source_secant N d a b hk q hp ha hb hdx)

end FLT.Mazur.WeierstrassDividedDepth
