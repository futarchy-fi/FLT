/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentPairNaturality
public import FLT.Mazur.PolygonStageCoefficientChange

/-!
# Laurent evaluation on constant units in a smoothing stage

The lifted reduced polynomial evaluates to the constant lift of its original
evaluation. This permits faithful top-coefficient extraction over arbitrary
commutative algebras, including algebras with nilpotents.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentPairStageLift
open LaurentPairNaturality PolygonInfinitesimalStages PolygonScalingNaturality
variable {R S : Type*} [CommRing R] [CommRing S]

/-- Changing stages and evaluating on lifted units recovers the scalar lift of evaluation. -/
theorem pairEval₂_stageLift (f : R →+* S) (m : ℕ) (u v : Sˣ)
    (p : R[T;T⁻¹][T;T⁻¹]) :
    pairEval₂ (stageCoefficientMap f m)
        (Units.map (algebraMap S (Ring S m)).toMonoidHom u)
        (Units.map (algebraMap S (Ring S m)).toMonoidHom v)
        (coeffMap (coeffMap (algebraMap R (Ring R m))) p) =
      algebraMap S (Ring S m) (pairEval₂ f u v p) := by
  have hc := congrArg (fun F : R[T;T⁻¹][T;T⁻¹] →+* Ring S m ↦ F p)
    (pairEval₂_coeffMap (algebraMap R (Ring R m)) (stageCoefficientMap f m)
      (Units.map (algebraMap S (Ring S m)).toMonoidHom u)
      (Units.map (algebraMap S (Ring S m)).toMonoidHom v))
  change pairEval₂ (stageCoefficientMap f m) _ _ _ = _ at hc
  rw [hc, stageCoefficientMap_comp_scalar]
  exact (congrArg (fun F : R[T;T⁻¹][T;T⁻¹] →+* Ring S m ↦ F p)
    (pairEval₂_map f (algebraMap S (Ring S m)) u v)).symm

end FLT.Mazur.LaurentPairStageLift
