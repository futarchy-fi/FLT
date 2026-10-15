/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalTopCoefficient
public import FLT.Mazur.PolygonStageCoefficientNaturality

/-!
# Scalar change for the concrete infinitesimal coefficient stages

A coefficient homomorphism extends to the truncated smoothing ring while
preserving its parameter. The top parameter layer faithfully retains every
coefficient, even over a nonreduced target ring.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonInfinitesimalStages
variable {R S : Type*} [CommRing R] [CommRing S]

/-- The square of coefficient inclusions and stage change commutes as ring homomorphisms. -/
theorem stageCoefficientMap_comp_scalar (f : R →+* S) (m : ℕ) :
    (stageCoefficientMap f m).comp (algebraMap R (Ring R m)) =
      (algebraMap S (Ring S m)).comp f :=
  RingHom.ext (stageCoefficientMap_constant f m)

/-- Extracting the first smoothing coefficient recovers an arbitrary scalar exactly. -/
theorem stageCoeff_one_parameter_scalar (s : S) :
    stageCoeff S 1 1 (parameter S 1 * algebraMap S (Ring S 1) s) = s := by
  simpa only [pow_one, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] using
    stageCoeff_top_mul S 1 (algebraMap S (Ring S 1) s)

/-- The first top-layer embedding is faithful over every commutative coefficient ring. -/
theorem parameter_scalar_one_injective :
    Function.Injective (fun s : S ↦ parameter S 1 * algebraMap S (Ring S 1) s) := by
  intro s t he
  have hh := congrArg (stageCoeff S 1 1) he
  simpa only [stageCoeff_one_parameter_scalar] using hh

end FLT.Mazur.PolygonInfinitesimalStages
