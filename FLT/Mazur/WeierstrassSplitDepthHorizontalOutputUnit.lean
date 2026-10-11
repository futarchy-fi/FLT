/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitDepthOriginalFractionAction

/-!
# Output horizontal units before selecting the output quotient open

An original horizontal input with retained denominator equal to its original
X coordinate has quotient one. On either exceptional branch the conormal
character therefore makes the output X quotient a residue unit. This is
proved on the original presentation, before any output quotient is inverted.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassIntegralChart
open IsLocalRing WeierstrassDividedDepth RegularCenter
open WeierstrassModificationReesCoordinates BlowupFractionChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S C : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  [CommRing S] [Algebra R S] [CommRing C]
  {W : WeierstrassCurve R} {π : R} {depth k : ℕ}
  (D : SplitNodeDepth W π depth) (d : Data W π k) (hk : 2 * k ≤ depth)
  (b : Bool) (f : additionChartRing W (ordinaryIndex b) →ₐ[R] S)
local notation "I₀" => modificationChartCenter W (π ^ k) 2
local notation "I" => Ideal.map
  (AlgHom.toRingHom (AlgHom.comp f (ordinaryInputRight W b)))
  (modificationChartCenter W (π ^ k) 2)
local notation "x" => f (ordinaryInputRight W b (coord W 2 0))
local notation "y" => f (ordinaryInputRight W b (coord W 2 1))
local notation "X" => f (ordinaryChartAddition W b (coord W 2 0))
local notation "a" => algebraMap R S W.a₁
local notation "H" => splitDepthExceptional_coordinates_mem d b f
variable (hI : ((modificationChartCenter W (π ^ k) 2).map
    (f.comp (ordinaryInputRight W b)).toRingHom).map (RingHom.id S) =
      Ideal.span {f (ordinaryInputRight W b (coord W 2 0))})
  (hx : IsRegular (f (ordinaryInputRight W b (coord W 2 0))))
  (L : chart (modificationChartCenter W (π ^ k) 2) (coord W 2 0) →+* S)
  (hL : ∀ t, L (algebraMap (Coordinate W 2) _ t) = f (ordinaryInputRight W b t))
  (e : S →+* C) (he : e (f (ordinaryInputRight W b (coord W 2 0))) = 0)
  (hJ : (maximalIdeal R).map (algebraMap R S) ≤ RingHom.ker e)
  (r q : Cˣ)
  (hr : e (f (ordinaryInputLeft W b (coord W 2 0))) = (r : C) * q)
  (hy : e (f (ordinaryInputLeft W b (coord W 2 1))) = (r : C) ^ 2 * q)
  (hq : (q : C) = (r : C) + e (algebraMap R S W.a₁))
local notation "Q" => quotient I (RingHom.id S) x hI

omit [IsDomain R] [IsLocalRing R] in
include hx in
/-- The retained original X coordinate has quotient one before residue restriction. -/
theorem splitDepthHorizontal_input_one : Q x (H).1.1 = 1 := by
  symm
  apply quotient_unique _ _ _ _ hx
  exact mul_one _

omit [IsDomain R] [IsLocalRing R] in
include hx hL in
/-- The original Y/X fraction is precisely the divided input Y coordinate. -/
theorem splitDepthHorizontal_input_vertical :
    L (horizontalVertical W (π ^ k)) = Q y (H).1.2 := by
  have h := originalLift_ratio_quotient I₀ I (f.comp (ordinaryInputRight W b)).toRingHom
    (RingHom.id S) x hI hx (coord W 2 0) (H).1.1 L hL
    (coord W 2 1) (centerGenerators_mem W (π ^ k) 2) (H).1.2
  change Q x (H).1.1 * L (horizontalVertical W (π ^ k)) = Q y (H).1.2 at h
  rw [splitDepthHorizontal_input_one d b f hI hx, one_mul] at h
  exact h

include D hk hx hL he hJ hr hy hq in
/-- On either original branch, the output horizontal quotient is already a residue unit. -/
theorem splitDepthHorizontal_output_unit
    (hbranch : e (L (horizontalVertical W (π ^ k))) = 0 ∨
      e (L (horizontalVertical W (π ^ k))) = -e (algebraMap R S W.a₁)) :
    IsUnit (e (Q X (H).2.1)) := by
  have hcomp : (maximalIdeal R).map (algebraMap R S) ≤
      RingHom.ker (e.comp (RingHom.id S)) := hJ
  rcases hbranch with h0 | h0
  · rw [splitDepthHorizontal_input_vertical d b f hI hx L hL] at h0
    have hX := (splitDepthExceptional_first_horizontal D d hk b f (RingHom.id S)
      x hI hx e he hcomp r q hr hy hq h0).2
    rw [splitDepthHorizontal_input_one d b f hI hx, map_one, mul_one] at hX
    rw [hX]
    exact (r * q⁻¹).isUnit
  · have hzero : e (Q (y + a * x) ((I).add_mem (H).1.2
        ((I).mul_mem_left a (H).1.1))) = 0 := by
      rw [quotient_add_mul I (RingHom.id S) x hI hx x y a (H).1.1 (H).1.2,
        map_add, map_mul, splitDepthHorizontal_input_one d b f hI hx, map_one, mul_one,
        ← splitDepthHorizontal_input_vertical d b f hI hx L hL, h0]
      exact neg_add_cancel _
    have hX := (splitDepthExceptional_second_horizontal D d hk b f (RingHom.id S)
      x hI hx e he hcomp r q hr hy hq hzero).2
    rw [splitDepthHorizontal_input_one d b f hI hx, map_one, mul_one] at hX
    rw [hX]
    exact (q * r⁻¹).isUnit

end FLT.Mazur.WeierstrassIntegralChart
