/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedWiderReflectedContraction
public import FLT.Mazur.WeierstrassDividedReflectedContraction
public import FLT.Mazur.WeierstrassDilatationLifting

/-!
# Agreement of the two reflected numerator presentations

At the common boundary m=k+2*l both constructions have the same target
and the same original source. Regularity identifies their entire algebra
maps, and hence their scheme morphisms, including on the closed fiber.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [IsDomain R] [IsLocalRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {k l m : ℕ} (D : SplitNodeDepth W π m)
  (d : Data W π k) (e : Data W π l) (hkl : k ≤ l)
  (hm : k + 2 * l ≤ m) (htop : m ≤ 2 * (k + l))
  (hl : 2 * l ≤ m) (hnear : m ≤ k + 2 * l)
  (z : Data W π (m - k - l)) (h2 : W.a₂ = 0)
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (c : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] S)
local notation "B" => SumDepthSourceRing d e a c

/-- The wider and near-terminal formulas agree as complete algebra maps on their overlap. -/
theorem widerReflectedSourceOutput_eq_near :
    widerReflectedSourceOutput d e a c D hkl hm htop z h2 =
      reflectedSourceOutput d e a c D hkl hl hnear z h2 := by
  have hreg : IsRegular (algebraMap R B (π ^ (m - k - l))) :=
    WeierstrassIntegralChart.flatRingHom_isRegular _
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
      (isRegular_iff_ne_zero.mpr (pow_ne_zero _ D.uniformizer_ne_zero))
  apply lift_unique W (π ^ (m - k - l)) z.b3 z.b4 z.b6
    z.factor3 z.factor4 z.factor6 hreg
  rw [widerReflectedSourceOutput_original, reflectedSourceOutput_original]

/-- The actual scheme-valued outputs agree on the entire unchanged principal open. -/
theorem widerReflectedSourceLift_eq_near :
    widerReflectedSourceLift d e a c D hkl hm htop z h2 =
      reflectedSourceLift d e a c D hkl hl hnear z h2 := by
  unfold widerReflectedSourceLift reflectedSourceLift
  rw [widerReflectedSourceOutput_eq_near D d e hkl hm htop hl hnear z h2 a c]

end FLT.Mazur.WeierstrassDividedDepth
