/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupOverlapLocalization

/-!
# Coordinates of the localized subgroup closure transition

The opposite chart's normalizing coordinate is the inverse of the overlap
parameter. These formulas expose the transition without unfolding its quotients.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.EllipticSubgroupChart

open WeierstrassIntegralChart

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) (j k : Fin 3)

/-- The inverse parameter agrees with the ambient overlap inverse modulo the equations. -/
theorem closureLocalizationEquiv_inverse :
    closureLocalizationEquiv A W H j k
        (IsLocalization.Away.invSelf (closureCoord A W H j k)) =
      Ideal.Quotient.mk _ (overlapInverse W j k) := by
  have hu := IsLocalization.map_units (LocalizedClosure A W H j k)
    (⟨closureCoord A W H j k, Submonoid.mem_powers _⟩)
  apply (hu.map (closureLocalizationEquiv A W H j k).toMonoidHom).mul_left_inj.mp
  change closureLocalizationEquiv A W H j k _ *
      closureLocalizationEquiv A W H j k
        (algebraMap (Closure A W H j) (LocalizedClosure A W H j k)
          (closureCoord A W H j k)) = _ * closureLocalizationEquiv A W H j k _
  rw [← map_mul, mul_comm (IsLocalization.Away.invSelf _),
    IsLocalization.Away.mul_invSelf, map_one, closureLocalizationEquiv_coord, ← map_mul,
    overlapInverse_mul, map_one]

/-- The descended transition rescales each homogeneous coordinate. -/
theorem localizedClosureEquiv_coord (i : Fin 3) :
    localizedClosureEquiv A W H j k
        (algebraMap (Closure A W H k) (LocalizedClosure A W H k j)
          (closureCoord A W H k i)) =
      IsLocalization.Away.invSelf (closureCoord A W H j k) *
        algebraMap (Closure A W H j) (LocalizedClosure A W H j k)
          (closureCoord A W H j i) := by
  apply (closureLocalizationEquiv A W H j k).injective
  simp only [localizedClosureEquiv, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply]
  rw [closureLocalizationEquiv_coord, closureOverlapEquiv_mk, transition_coord,
    map_mul, map_mul, closureLocalizationEquiv_inverse, closureLocalizationEquiv_coord]

/-- The chart's own normalizing coordinate is one. -/
@[simp] theorem closureCoord_self : closureCoord A W H j j = 1 := by
  change Ideal.Quotient.mk _ (coord W j j) = 1
  rw [coord_self, map_one]

/-- The other chart supplies the inverse of the overlap parameter. -/
theorem localizedClosureEquiv_normalizer :
    localizedClosureEquiv A W H j k
        (algebraMap (Closure A W H k) (LocalizedClosure A W H k j)
          (closureCoord A W H k j)) =
      IsLocalization.Away.invSelf (closureCoord A W H j k) := by
  rw [localizedClosureEquiv_coord, closureCoord_self, map_one, mul_one]

end FLT.Mazur.EllipticSubgroupChart
