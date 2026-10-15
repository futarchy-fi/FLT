/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonFirstNodeParameterDescent

/-!
# Laurent substitution on the first parameter layer

Two full Laurent units with the same closed reduction act identically on
every parameter-weighted Laurent function. This applies to arbitrary
functions, including negative powers, before any extension across a node.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open LaurentPolynomial LaurentUnitPoints PolygonScalingNaturality
variable (R : Type) [CommRing R]
local notation "S" => Ring R 1
local notation "e" => parameter R 1
local notation "L" => (S)[T;T⁻¹]
local notation "r" => coeffMap (AlgHom.toRingHom (reduction R 1))

/-- The closed Laurent substitution depends only on the closed value of its unit coordinate. -/
theorem firstLaurent_evalUnit_reduction_eq (u v : (L)ˣ)
    (huv : (r) u.val = (r) v.val) (p : L) :
    (r) (evalUnit u p) = (r) (evalUnit v p) := by
  have he : Units.map (r).toMonoidHom u = Units.map (r).toMonoidHom v :=
    Units.ext huv
  have hi : (r) u⁻¹.val = (r) v⁻¹.val :=
    congrArg (fun w : R[T;T⁻¹]ˣ ↦ w⁻¹.val) he
  have hm : (r).comp (evalUnit (R := S) u).toRingHom =
      (r).comp (evalUnit (R := S) v).toRingHom := by
    apply ringHom_ext
    · intro s
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, evalUnit_C]
    · simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        evalUnit_T, zpow_one] using huv
    · simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        evalUnit_T, zpow_neg_one] using hi
  exact RingHom.congr_fun hm p

/-- Equal closed values force equality on every full parameter-weighted Laurent function. -/
theorem firstLaurent_evalUnit_parameter_eq (u v : (L)ˣ)
    (huv : (r) u.val = (r) v.val) (p : L) :
    C (e) * evalUnit u p = C (e) * evalUnit v p := by
  rw [firstLaurent_parameter_reduction R (evalUnit u p),
    firstLaurent_parameter_reduction R (evalUnit v p),
    firstLaurent_evalUnit_reduction_eq R u v huv]

/-- The two substitutions themselves agree on the entire parameter ideal. -/
theorem firstLaurent_evalUnit_weighted_eq (u v : (L)ˣ)
    (huv : (r) u.val = (r) v.val) (p : L) :
    evalUnit u (C (e) * p) = evalUnit v (C (e) * p) := by
  rw [map_mul, map_mul, evalUnit_C, evalUnit_C]
  exact firstLaurent_evalUnit_parameter_eq R u v huv p

/-- In particular every canonical parameter-layer lift has the same image under both units. -/
theorem firstLaurent_evalUnit_parameterLift_eq (u v : (L)ˣ)
    (huv : (r) u.val = (r) v.val) (p : R[T;T⁻¹]) :
    evalUnit u (firstLaurentParameterLift R p) =
      evalUnit v (firstLaurentParameterLift R p) :=
  firstLaurent_evalUnit_weighted_eq R u v huv _

end FLT.Mazur.PolygonInfinitesimalStages
