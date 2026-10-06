/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicNegationOverlap

/-! # Comparing algebra-valued points in the two cubic charts

An explicit pair of reciprocal coordinate identities suffices to identify
the induced scheme morphisms. This is the gluing criterion for addition
formulas whose outputs use different affine charts. -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Affine and infinity coordinates satisfying the transition identities give the same
morphism into the glued cubic. -/
theorem chart_point_agreement {S : Type u} [CommRing S] [Algebra R S]
    (f : Ring W false →ₐ[R] S) (g : Ring W true →ₐ[R] S)
    (hy : f (coord W false 1) * g (coord W true 1) = 1)
    (hx : f (coord W false 0) * g (coord W true 1) = g (coord W true 0)) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ affineChart W =
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ infinityChart W := by
  have hu : IsUnit (g (coord W true 1)) :=
    isUnit_iff_exists_inv.mpr ⟨f (coord W false 1), by rw [mul_comm, hy]⟩
  let h : Overlap W true →ₐ[R] S := IsLocalization.Away.liftAlgHom (coord W true 1) (f := g) hu
  have hl (x : Ring W true) :
      h (algebraMap (Ring W true) (Overlap W true) x) = g x := by
    simp [h, IsLocalization.Away.liftAlgHom_apply]
  have hloc (i : Fin 2) : h (loc W true i) = g (coord W true i) := hl _
  have hinv : h (inv W true) = f (coord W false 1) := by
    have hm := congrArg h (loc_mul_inv W true)
    rw [map_mul, map_one, hloc] at hm
    linear_combination f (coord W false 1) * hm - h (inv W true) * hy
  have hc : h.comp (changeChart W true) = f := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    change h (changeChart W true (coord W (!true) i)) = f (coord W false i)
    rw [changeChart_coord]
    fin_cases i
    · change h (loc W true 0 * inv W true) = f (coord W false 0)
      rw [map_mul, hloc, hinv]
      linear_combination -f (coord W false 1) * hx + f (coord W false 0) * hy
    · change h (inv W true) = f (coord W false 1)
      exact hinv
  have hcf :
      Spec.map (CommRingCat.ofHom f.toRingHom) =
        Spec.map (CommRingCat.ofHom h.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (changeChart W true).toRingHom) := by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact (DFunLike.congr_fun hc x).symm
  rw [hcf, Category.assoc, changeChart_true_to_scheme]
  unfold overlapInclusion
  rw [← Category.assoc, ← Spec.map_comp]
  congr 1
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext hl

end WeierstrassCurve.CubicCharts
