/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRetainedFixedEdgeUnit
public import FLT.Mazur.WeierstrassRetainedFixedNaturality
public import FLT.Mazur.PolygonSmoothingRingMapBranch

/-!
# Naturality of the full outgoing retained unit

The coefficient map transports every factor in the outgoing parameter,
including the full node correction. The induced Laurent evaluation square
will also transport the reciprocal parameter and its constructed inverse.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
open PolygonSmoothing PolygonScalingNaturality
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  (π : R) (π' : S) (hπ : f π = π')
  (q : Rˣ) (U : (ChartRing π)ˣ) (U' : (ChartRing π')ˣ)
  (hU : Units.map (ringMap f π π' hπ).toMonoidHom U = U')

include hU in
/-- Every factor of the actual outgoing unit follows the coefficient map. -/
theorem retainedFixedEdgeUnit_coefficients :
    Units.map (coeffMap f).toMonoidHom (retainedFixedEdgeUnit π q U) =
      retainedFixedEdgeUnit π' (Units.map f.toMonoidHom q) U' := by
  have hi := congrArg (fun v : (ChartRing π')ˣ ↦ (↑v⁻¹ : ChartRing π')) hU
  change ringMap f π π' hπ (↑U⁻¹ : ChartRing π) = (↑(U')⁻¹ : ChartRing π') at hi
  apply Units.ext
  change coeffMap f (retainedFixedEdgeUnit π q U : R[T;T⁻¹]) = _
  rw [retainedFixedEdgeUnit_val, map_mul, map_mul]
  change coeffMap f (LaurentPolynomial.C (q : R)) *
      coeffMap f (LaurentPolynomial.T 1) * _ = _
  rw [coeffMap_C, coeffMap_T_one, retainedFixedEdgeUnit_val]
  congr 1
  have he := congrArg (fun g : ChartRing π →+* S[T;T⁻¹] ↦ g (↑U⁻¹ : ChartRing π))
    (ringMap_leftLaurent f π π' hπ)
  exact he.symm.trans (congrArg (leftLaurentMap π') hi)

end FLT.Mazur.WeierstrassModificationX

namespace FLT.Mazur.LaurentUnitPoints
open PolygonScalingNaturality
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  (v : R[T;T⁻¹]ˣ) (w : S[T;T⁻¹]ˣ)
  (hv : Units.map (coeffMap f).toMonoidHom v = w)
include hv

/-- Full Laurent substitutions commute with coefficient change when their units do. -/
theorem evalUnit_coefficients :
    (coeffMap f).comp (evalUnit (R := R) v).toRingHom =
      (evalUnit (R := S) w).toRingHom.comp (coeffMap f) := by
  have hp := congrArg Units.val hv
  have hn := congrArg (fun z : S[T;T⁻¹]ˣ ↦ (↑z⁻¹ : S[T;T⁻¹])) hv
  change coeffMap f (v : R[T;T⁻¹]) = (w : S[T;T⁻¹]) at hp
  change coeffMap f (↑v⁻¹ : R[T;T⁻¹]) = (↑w⁻¹ : S[T;T⁻¹]) at hn
  apply ringHom_ext
  · intro r
    change coeffMap f (evalUnit v (LaurentPolynomial.C r)) =
      evalUnit w (coeffMap f (LaurentPolynomial.C r))
    rw [evalUnit_C, coeffMap_C, evalUnit_C]
    exact coeffMap_C f r
  · simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      evalUnit_T, zpow_one, coeffMap_T_one] using hp
  · simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      evalUnit_T, zpow_neg_one, coeffMap_T_neg_one] using hn

end FLT.Mazur.LaurentUnitPoints
