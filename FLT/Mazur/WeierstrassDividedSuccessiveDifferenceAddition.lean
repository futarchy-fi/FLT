/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSuccessiveZeroMixedCoverage

/-!
# Unequal tensor outputs requiring only the difference stage

The actual unequal-depth secant lands at the difference of the input depths.
It does not need a final model containing their sum. The integral flat pair
supplies the formula, which then pulls back to the whole coefficient algebra.
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
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {k l n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (d : Data W π k) (d' : Data W π (k + 1))
  (e : Data W π l) (e' : Data W π (l + 1))
  (S : Type) [CommRing S] [Algebra R S] (hkl : k ≤ l)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (j : ℕ) (hj : j ≤ n) (hdiff : l - k ≤ j)
local notation "hπ" => node.uniformizer_ne_zero
local notation "P" => SuccessiveTensorPairRing d' e' S
local notation "f" => successiveTensorPairInput hπ d d' e e' S
local notation "input" => Spec.map (CommRingCat.ofHom (f).toRingHom)
local notation "a" => unequalPairLeft d e
local notation "b" => unequalPairRight d e
local notation "V" => unequalDepthDomain hπ d e hkl data (hdiff.trans hj) a b
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus

/-- The actual unequal-depth domain with only the difference-stage bound. -/
def successiveDifferenceOpen : (Spec (.of P)).Opens := input ⁻¹ᵁ V

local notation "D" => successiveDifferenceOpen node d d' e e' S hkl data j hj hdiff

/-- The constructed unequal-depth sum promotes from its actual difference stage. -/
def successiveDifferenceAddition : (D).toScheme ⟶ (U).toScheme :=
  (input ∣_ V) ≫ unequalDepthResolvedAddition hπ d e hkl data (hdiff.trans hj)
    a b j hj hdiff

/-- The entire resolved output preserves the original tensor coefficient morphism. -/
@[reassoc] theorem successiveDifferenceAddition_structure :
    successiveDifferenceAddition node d d' e e' S hkl data j hj hdiff ≫ (U).ι ≫ base =
      (D).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R P)) := by
  rw [successiveDifferenceAddition, Category.assoc, unequalDepthResolvedAddition_structure,
    morphismRestrict_ι_assoc, successiveTensorPairInput_structure]
  rfl

variable (m : ℕ)
local notation "Q" => Quotient R π m
local notation "T" => SuccessiveTensorPairRing d' e' Q
local notation "g" => successiveTensorPairInput hπ d d' e e' Q
local notation "u₁" => successiveTensorPairLeft d' e' Q
  (tensorCoord W (π ^ k) π d'.b3 d'.b4 d'.b6 Q 2)
local notation "u₂" => successiveTensorPairRight d' e' Q
  (tensorCoord W (π ^ l) π e'.b3 e'.b4 e'.b6 Q 2)
local notation "y₁" => g (a (y W (π ^ k) d.b3 d.b4 d.b6))
local notation "y₂" => g (b (y W (π ^ l) e.b3 e.b4 e.b6))
local notation "α" => algebraMap R T W.a₁

/-- Opposite punctured branches are covered without any doubled or sum-depth data. -/
theorem successiveDifference_opposite_mem (hk : 0 < k) (hlt : k < l) (hm : 2 * l < depth)
    (p : PrimeSpectrum T) (hx : u₁ ∉ p.asIdeal) (hu : u₂ ∉ p.asIdeal)
    (hb : (y₁ ∈ p.asIdeal ∧ y₂ + α * u₂ ∈ p.asIdeal) ∨
      (y₁ + α * u₁ ∈ p.asIdeal ∧ y₂ ∈ p.asIdeal)) :
    p ∈ successiveDifferenceOpen node d d' e e' Q hkl data j hj hdiff := by
  let q := PrimeSpectrum.comap (g).toRingHom p
  have hp : algebraMap R (UnequalPairRing d e) π ∈ q.asIdeal := by
    change g (algebraMap R (UnequalPairRing d e) π) ∈ p.asIdeal
    rw [AlgHom.commutes]
    exact arithmeticPrime_parameter_mem π m T p
  have hx' : a (x W (π ^ k) d.b3 d.b4 d.b6) ∉ q.asIdeal := by
    change g (a _) ∉ p.asIdeal
    rwa [successiveTensorPairInput_left_apply, successiveTensorInput_x]
  have hu' : b (x W (π ^ l) e.b3 e.b4 e.b6) ∉ q.asIdeal := by
    change g (b _) ∉ p.asIdeal
    rwa [successiveTensorPairInput_right_apply, successiveTensorInput_x]
  apply unequalDepthDomain_opposite_mem node d e hkl data (hdiff.trans hj)
    a b hk hlt hm q hp hx' hu'
  change (g (a _) ∈ p.asIdeal ∧ g (b _ + _ * b _) ∈ p.asIdeal) ∨
    (g (a _ + _ * a _) ∈ p.asIdeal ∧ g (b _) ∈ p.asIdeal)
  simpa only [map_add, map_mul, AlgHom.commutes,
    successiveTensorPairInput_left_apply, successiveTensorPairInput_right_apply,
    successiveTensorInput_x] using hb

local notation "v₁" => successiveTensorPairLeft d' e' Q
  (tensorCoord W (π ^ k) π d'.b3 d'.b4 d'.b6 Q 1)
local notation "v₂" => successiveTensorPairRight d' e' Q
  (tensorCoord W (π ^ l) π e'.b3 e'.b4 e'.b6 Q 1)

/-- Opposite branches can be tested directly in the full tensor charts' slope coordinates. -/
theorem successiveDifference_opposite_slopes_mem
    (hk : 0 < k) (hlt : k < l) (hm : 2 * l < depth)
    (p : PrimeSpectrum T) (hx : u₁ ∉ p.asIdeal) (hu : u₂ ∉ p.asIdeal)
    (hb : (v₁ ∈ p.asIdeal ∧ v₂ + α ∈ p.asIdeal) ∨
      (v₁ + α ∈ p.asIdeal ∧ v₂ ∈ p.asIdeal)) :
    p ∈ successiveDifferenceOpen node d d' e e' Q hkl data j hj hdiff := by
  apply successiveDifference_opposite_mem node d d' e e' hkl data j hj hdiff
    m hk hlt hm p hx hu
  simp only [successiveTensorPairInput_left_apply, successiveTensorPairInput_right_apply,
    successiveTensorInput_y, map_mul]
  rcases hb with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · refine Or.inl ⟨p.asIdeal.mul_mem_left _ ha, ?_⟩
    convert p.asIdeal.mul_mem_left u₂ hb using 1
    ring
  · refine Or.inr ⟨?_, p.asIdeal.mul_mem_left _ hb⟩
    convert p.asIdeal.mul_mem_left u₁ ha using 1
    ring

end FLT.Mazur.WeierstrassDividedDepth
