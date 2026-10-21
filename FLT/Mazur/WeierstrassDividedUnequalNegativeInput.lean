/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedUnequalDepthSecant
public import FLT.Mazur.WeierstrassDividedNegativeSecantScheme

/-!
# Negation commutes with contraction to unequal input depths

The actual right input can be negated before or after contraction to the
left depth. The coefficient factorization proves equality of the entire
coordinate maps, without cancelling any scale in the input algebra.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k l : ℕ}
  (d : Data W π k) (e : Data W π l) (hkl : k ≤ l)
  (c : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] S)

/-- Unequal-depth contraction intertwines the actual divided negations. -/
theorem unequalDepthRight_negative :
    unequalDepthRight hπ d e hkl (branchNegativeInput W (π ^ l) e.b3 e.b4 e.b6 c) =
      branchNegativeInput W (π ^ k) d.b3 d.b4 d.b6
        (unequalDepthRight hπ d e hkl c) := by
  apply hom_ext
  · simp only [unequalDepthRight_x, branchNegativeInput_x]
  · simp only [unequalDepthRight_y, branchNegativeInput_y,
      unequalDepthRight_x, depth_coefficient_factor π k l hπ hkl d.factor3 e.factor3,
      map_mul]
    ring

open AlgebraicGeometry CategoryTheory
variable (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "a'" => branchNegativeInput W (π ^ k) d.b3 d.b4 d.b6 a
local notation "c'" => branchNegativeInput W (π ^ l) e.b3 e.b4 e.b6 c
local notation "c₀" => unequalDepthRight hπ d e hkl c
local notation "c₀'" => unequalDepthRight hπ d e hkl c'
local notation "T" => UnequalDepthSecantRing hπ d e hkl a c
local notation "T'" => UnequalDepthSecantRing hπ d e hkl a' c'
local notation "it" => Spec.map (CommRingCat.ofHom (algebraMap S T))
local notation "it'" => Spec.map (CommRingCat.ofHom (algebraMap S T'))

/-- The unequal-depth negative secant recovers the original sum on every common source. -/
theorem unequalNegativeSecant_scheme {X : Scheme.{u}}
    (p : X ⟶ Spec (.of T')) (q : X ⟶ Spec (.of T)) (hpq : p ≫ it' = q ≫ it) :
    p ≫ dividedSecantToCurve W (π ^ k) d.b3 d.b4 d.b6 a' c₀'
        d.factor3 d.factor4 d.factor6 ≫
          WeierstrassIntegralChart.integralCurveNegation W =
      q ≫ dividedSecantToCurve W (π ^ k) d.b3 d.b4 d.b6 a c₀
        d.factor3 d.factor4 d.factor6 := by
  revert p
  simp only [UnequalDepthSecantRing]
  rw [unequalDepthRight_negative]
  intro p hpq
  exact dividedNegativeSecant_scheme W (π ^ k) d.b3 d.b4 d.b6 a c₀
    d.factor3 d.factor4 d.factor6 p q hpq

end FLT.Mazur.WeierstrassDividedDepth
