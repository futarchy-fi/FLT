/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonPowerSeriesBase

/-!
# Coefficient naturality of the original truncated bases

Every coefficient-ring homomorphism induces maps of the actual stage rings.
They retain the specified parameter, restrictions and power-series evaluations.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonInfinitesimalStages
open Polynomial
variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

/-- The coefficient map on the original truncated polynomial ring. -/
def stageCoefficientMap (f : R →+* S) (m : ℕ) : Ring R m →+* Ring S m :=
  AdjoinRoot.map f (X ^ (m + 1)) (X ^ (m + 1)) (by simp)

/-- Coefficient change retains the actual smoothing parameter. -/
@[simp] theorem stageCoefficientMap_parameter (f : R →+* S) (m : ℕ) :
    stageCoefficientMap f m (parameter R m) = parameter S m := by
  exact AdjoinRoot.map_root _ _ _ _

/-- Coefficient change acts on constants by the original ring homomorphism. -/
theorem stageCoefficientMap_constant (f : R →+* S) (m : ℕ) (r : R) :
    stageCoefficientMap f m (algebraMap R (Ring R m) r) =
      algebraMap S (Ring S m) (f r) := by
  exact AdjoinRoot.map_of _ _ _ _ r

/-- Identity coefficient change is the identity on every original stage ring. -/
theorem stageCoefficientMap_id (m : ℕ) :
    stageCoefficientMap (RingHom.id R) m = RingHom.id (Ring R m) := by
  apply AdjoinRoot.ringHom_ext
  · ext r
    exact stageCoefficientMap_constant (RingHom.id R) m r
  · exact stageCoefficientMap_parameter (RingHom.id R) m

/-- The original stage maps compose with the coefficient-ring homomorphisms. -/
theorem stageCoefficientMap_comp (f : R →+* S) (g : S →+* T) (m : ℕ) :
    (stageCoefficientMap g m).comp (stageCoefficientMap f m) =
      stageCoefficientMap (g.comp f) m :=
  AdjoinRoot.map_comp_map _ _ _ _ _ _ _

/-- The actual coefficient map commutes with the original successive restriction. -/
theorem stageCoefficientMap_restriction (f : R →+* S) (m : ℕ) :
    (restriction S m).toRingHom.comp (stageCoefficientMap f (m + 1)) =
      (stageCoefficientMap f m).comp (restriction R m).toRingHom := by
  apply AdjoinRoot.ringHom_ext
  · ext r
    change restriction S m (stageCoefficientMap f (m + 1)
      (algebraMap R (Ring R (m + 1)) r)) =
        stageCoefficientMap f m (restriction R m (algebraMap R (Ring R (m + 1)) r))
    simp only [stageCoefficientMap_constant, AlgHom.commutes]
  · change restriction S m (stageCoefficientMap f (m + 1) (parameter R (m + 1))) =
      stageCoefficientMap f m (restriction R m (parameter R (m + 1)))
    rw [stageCoefficientMap_parameter, restriction_parameter, restriction_parameter,
      stageCoefficientMap_parameter]

/-- A polynomial representative is changed by its original coefficient map. -/
theorem stageCoefficientMap_mk (f : R →+* S) (m : ℕ) (p : R[X]) :
    stageCoefficientMap f m (AdjoinRoot.mk _ p) = AdjoinRoot.mk _ (p.map f) := by
  have he : (stageCoefficientMap f m).comp (AdjoinRoot.mk _) =
      (AdjoinRoot.mk _).comp (Polynomial.mapRingHom f) := by
    ext r <;> simp [stageCoefficientMap]
  exact DFunLike.congr_fun he p

/-- Evaluation of a complete coefficient series commutes with every coefficient change. -/
theorem stageCoefficientMap_seriesToStage (f : R →+* S) (m : ℕ) (s : PowerSeries R) :
    stageCoefficientMap f m (seriesToStage R m s) =
      seriesToStage S m (s.map f) := by
  change stageCoefficientMap f m (AdjoinRoot.mk _ (s.trunc (m + 1))) =
    AdjoinRoot.mk _ ((s.map f).trunc (m + 1))
  rw [stageCoefficientMap_mk, PowerSeries.trunc_map]

end FLT.Mazur.PolygonInfinitesimalStages
