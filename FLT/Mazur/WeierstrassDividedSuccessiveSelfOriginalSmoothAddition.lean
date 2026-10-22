/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSuccessiveSelfDeepAddition
public import FLT.Mazur.WeierstrassDividedZeroOriginalSmoothCoverage

/-!
# Original smooth addition on full equal successive tensor pairs

The actual original smooth law lifts to the unchanged resolved model.
At creation depth zero its domain contains all punctured arithmetic pairs,
including coincident and self-inverse inputs in arbitrary characteristic.
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
  (j : ℕ) (hj : j ≤ n)
local notation "hπ" => node.uniformizer_ne_zero
local notation "P" => SuccessiveTensorPairRing e e S
local notation "f" => successiveTensorPairInput hπ d e d e S
local notation "input" => Spec.map (CommRingCat.ofHom (f).toRingHom)
local notation "a" => unequalPairLeft d d
local notation "b" => unequalPairRight d d
local notation "O" => suppliedOriginalSmoothDomain d a b
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus

/-- The original smooth output domain in the whole equal-depth tensor pair. -/
def successiveSelfOriginalSmoothOpen : (Spec (.of P)).Opens := input ⁻¹ᵁ O

local notation "D" => successiveSelfOriginalSmoothOpen node d e S

/-- The original smooth formula has its actual output in the supplied final smooth model. -/
def successiveSelfOriginalSmoothAddition : (D).toScheme ⟶ (U).toScheme :=
  (input ∣_ O) ≫ suppliedOriginalSmoothResolvedAddition d a b hπ data j hj

/-- The original smooth output preserves the whole original coefficient morphism. -/
@[reassoc] theorem successiveSelfOriginalSmoothAddition_structure :
    successiveSelfOriginalSmoothAddition node d e S data j hj ≫ (U).ι ≫ base =
      (D).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R P)) := by
  rw [successiveSelfOriginalSmoothAddition, Category.assoc,
    suppliedOriginalSmoothResolvedAddition_structure,
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

omit [IsBezout R] [IsNoetherianRing R] in
/-- Both zero-depth punctured arithmetic inputs reach an actual output, even on the diagonal. -/
theorem successiveSelfOriginalSmooth_zero_punctured (hk : k = 0) (hd : 0 < depth)
    (p : PrimeSpectrum T) (hx : u₁ ∉ p.asIdeal) (hu : u₂ ∉ p.asIdeal) :
    p ∈ successiveSelfOriginalSmoothOpen node d e Q := by
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
  exact suppliedOriginalSmoothDomain_zeroDepth_mem node d a b hk hd q hp hx' hu'

end FLT.Mazur.WeierstrassDividedDepth
