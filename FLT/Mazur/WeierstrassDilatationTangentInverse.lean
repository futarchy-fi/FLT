/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationPolynomialTangents
public import FLT.Mazur.WeierstrassModificationXNodeInverseParameter

/-!
# Recovering the original full terminal coordinates from the tangent factors

Finite nilpotent inversion recovers the horizontal coordinate from the tangent
difference, without localizing at x. The original vertical coordinate follows.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassDilatation
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (b3 : R) (r : R[X])
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (ha : IsUnit W.a₁)
  {S : Type*} [CommRing S] [Algebra R S] (p q : S)

/-- The full terminal horizontal coordinate is constructed by finite nilpotent inversion. -/
def terminalInverseX : S :=
  WeierstrassModificationX.polynomialNodeInverseT 0 r I hI hrI (I.zero_mem) W
    (q - p - algebraMap R S b3) 0 (by simpa only [zero_add] using ha.map (algebraMap R S))

local notation "T" => terminalInverseX W b3 r I hI hrI ha p q

/-- The inverse solves the unchanged terminal tangent-difference equation. -/
theorem terminalInverseX_equation :
    T * (algebraMap R S W.a₁ + r.eval₂ (algebraMap R S) T + r.eval₂ (algebraMap R S) T) =
      q - p - algebraMap R S b3 := by
  have h := WeierstrassModificationX.polynomialNodeInverseT_equation 0 r I hI hrI
    (I.zero_mem) W (q - p - algebraMap R S b3) 0
    (by simpa only [zero_add] using ha.map (algebraMap R S))
  simpa only [terminalInverseX, map_zero, zero_mul, zero_add, add_zero, ← add_assoc] using h

include hI hrI ha in
/-- The entire terminal tangent-difference equation has a unique horizontal solution. -/
theorem terminalInverseX_unique {z w : S}
    (hz : z * (algebraMap R S W.a₁ + r.eval₂ (algebraMap R S) z +
      r.eval₂ (algebraMap R S) z) = q - p - algebraMap R S b3)
    (hw : w * (algebraMap R S W.a₁ + r.eval₂ (algebraMap R S) w +
      r.eval₂ (algebraMap R S) w) = q - p - algebraMap R S b3) : z = w := by
  apply WeierstrassModificationX.polynomialNodeParameter_unique 0 r I hI hrI (I.zero_mem)
    W (q - p - algebraMap R S b3) 0
    (by simpa only [zero_add] using ha.map (algebraMap R S))
  · simpa only [map_zero, zero_mul, zero_add, add_zero, ← add_assoc] using hz
  · simpa only [map_zero, zero_mul, zero_add, add_zero, ← add_assoc] using hw

variable (s b4 b6 : R)
local notation "A" => Coordinate W s b3 b4 b6
local notation "P" => terminalSmallTangent W s b3 b4 b6 r
local notation "Q" => terminalOppositeTangent W s b3 b4 b6 r

/-- The constructed inverse recovers the original x on the entire terminal chart. -/
theorem terminalInverseX_original :
    terminalInverseX W b3 r I hI hrI ha P Q = x W s b3 b4 b6 := by
  apply terminalInverseX_unique W b3 r I hI hrI ha P Q
  · exact terminalInverseX_equation W b3 r I hI hrI ha P Q
  · have he : r.eval₂ (algebraMap R A) (x W s b3 b4 b6) = algebraMap R[X] A r :=
      Polynomial.eval₂_algebraMap_X r (Algebra.algHom R R[X] A)
    rw [he]
    exact (terminalTangents_difference W s b3 b4 b6 r).symm

/-- The small tangent and recovered x retain the original y, including at the origin. -/
theorem terminalInverseY_original :
    P + terminalInverseX W b3 r I hI hrI ha P Q * algebraMap R[X] A r =
      y W s b3 b4 b6 := by
  rw [terminalInverseX_original, terminalSmallTangent, sub_add_cancel]

end FLT.Mazur.WeierstrassDilatation
