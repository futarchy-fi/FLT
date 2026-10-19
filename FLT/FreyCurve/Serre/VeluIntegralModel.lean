/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluIntegralSums

/-!
# An integral equation for the Vélu target

The paired sums give a concrete equation over the chosen subring. Its generic
fiber is the original Vélu equation, and its special fibers retain the actual
coefficient sums under the specialization map.
-/

@[expose] public section

noncomputable section

namespace WeierstrassCurve.Velu

variable {K : Type*} [Field K] [DecidableEq K] [NeZero (2 : K)]
variable (S : Subring K) (W : WeierstrassCurve S)
variable (G : AddSubgroup (W.map S.subtype).toAffine.Point) [Fintype G]
variable (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)
variable (hx : ∀ Q : G, Q ≠ 0 → xCoord Q.val ∈ S)

/-- The first kernel sum as an element of the integral coefficient ring. -/
def integralT : S :=
  ⟨t (W.map S.subtype) G, t_mem_subring (W.map S.subtype) G hodd S
    (by rw [map_b₂]; exact (W.b₂).property)
    (by rw [map_b₄]; exact (W.b₄).property) hx⟩

/-- The second kernel sum as an element of the integral coefficient ring. -/
def integralW : S :=
  ⟨w (W.map S.subtype) G, w_mem_subring (W.map S.subtype) G hodd S
    (by rw [map_b₂]; exact (W.b₂).property)
    (by rw [map_b₄]; exact (W.b₄).property)
    (by rw [map_b₆]; exact (W.b₆).property) hx⟩

/-- The integral target equation constructed from the paired kernel sums. -/
def integralCurve : WeierstrassCurve S where
  a₁ := W.a₁
  a₂ := W.a₂
  a₃ := W.a₃
  a₄ := W.a₄ - 5 * integralT S W G hodd hx
  a₆ := W.a₆ - W.b₂ * integralT S W G hodd hx - 7 * integralW S W G hodd hx

/-- The constructed integral equation has exactly the prescribed generic fiber. -/
theorem integralCurve_map :
    (integralCurve S W G hodd hx).map S.subtype = curve (W.map S.subtype) G := by
  ext <;> rfl

/-- No second equation over this subring can have the same generic coefficients. -/
theorem integralCurve_unique (U : WeierstrassCurve S)
    (hU : U.map S.subtype = curve (W.map S.subtype) G) :
    U = integralCurve S W G hodd hx :=
  WeierstrassCurve.map_injective Subtype.val_injective
    (hU.trans (integralCurve_map S W G hodd hx).symm)

/-- Specialization is given by the specialized source and the two integral sums. -/
theorem integralCurve_specialization {k : Type*} [CommRing k] (f : S →+* k) :
    (integralCurve S W G hodd hx).map f =
      ⟨f W.a₁, f W.a₂, f W.a₃,
        f W.a₄ - 5 * f (integralT S W G hodd hx),
        f W.a₆ - f W.b₂ * f (integralT S W G hodd hx) -
          7 * f (integralW S W G hodd hx)⟩ := by
  ext <;> simp [integralCurve, map_ofNat]

end WeierstrassCurve.Velu
