/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassTripleChartOverlap

/-!
# The integral triple chart cocycle

Three cyclic normalizations compose to the identity on the entire triple
intersection. The proof only cancels units introduced by the principal opens;
it does not use reducedness, fields, smoothness or the discriminant.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (j k l : Fin 3)

/-- The product of the three transported normalizing factors is one. -/
theorem tripleTransition_inverse_product :
    tripleTransition W j k l (tripleTransition W k l j (tripleInverse W l j k)) *
      tripleTransition W j k l (tripleInverse W k l j) * tripleInverse W j k l = 1 := by
  have h := congrArg (fun x => tripleTransition W j k l (tripleTransition W k l j x))
    (tripleInverse_mul W l j k)
  simpa only [map_mul, map_one, tripleTransition_coord, tripleCoord_self,
    mul_one, mul_assoc] using h

/-- Cyclic chart changes satisfy the cocycle as actual algebra maps. -/
theorem tripleTransition_cocycle :
    (tripleTransition W j k l).comp
      ((tripleTransition W k l j).comp (tripleTransition W l j k)) =
        AlgHom.id R (TripleOverlap W j k l) := by
  apply tripleOverlap_hom_ext
  intro i
  simp only [AlgHom.comp_apply, AlgHom.id_apply, tripleTransition_coord, map_mul]
  calc
    _ = (tripleTransition W j k l
        (tripleTransition W k l j (tripleInverse W l j k)) *
        tripleTransition W j k l (tripleInverse W k l j) * tripleInverse W j k l) *
        tripleCoord W j k l i := by ring
    _ = tripleCoord W j k l i := by rw [tripleTransition_inverse_product, one_mul]

/-- A cyclic transition is an isomorphism; the other two transitions form its inverse. -/
def tripleOverlapEquiv : TripleOverlap W k l j ≃ₐ[R] TripleOverlap W j k l :=
  AlgEquiv.ofAlgHom (tripleTransition W j k l)
    ((tripleTransition W k l j).comp (tripleTransition W l j k))
    (tripleTransition_cocycle W j k l) (by
      rw [AlgHom.comp_assoc]
      exact tripleTransition_cocycle W k l j)

/-- The triple change restricts to the original pairwise chart transition. -/
theorem tripleTransition_pair :
    (tripleTransition W j k l).comp (tripleRight W k l j) =
      (tripleLeft W j k l).comp (transition W j k) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (coord W k j))
  apply hom_ext
  intro i
  change tripleTransition W j k l (tripleRight W k l j (overlapCoord W k j i)) =
    tripleLeft W j k l (transition W j k (overlapCoord W k j i))
  simp only [tripleRight_coord, tripleTransition_coord, transition_coord, map_mul,
    tripleLeft_coord, tripleInverse]

/-- Normalization at the coordinate already equal to one is the identity. -/
theorem transition_self : transition W j j = AlgHom.id R (Overlap W j j) := by
  have hi : overlapInverse W j j = 1 := by
    simpa only [overlapCoord_self, mul_one] using overlapInverse_mul W j j
  apply IsLocalization.algHom_ext (Submonoid.powers (coord W j j))
  apply hom_ext
  intro i
  change transition W j j (overlapCoord W j j i) = overlapCoord W j j i
  rw [transition_coord, hi, one_mul]

end FLT.Mazur.WeierstrassIntegralChart
