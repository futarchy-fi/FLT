/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonParameter
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Lifting the varying arithmetic parameter across nilpotent thickenings

Every lift of the original parameter lifts its classifying homomorphism.
This proves infinitesimal lifting for this algebraic parameter space; it does
not claim that every deformation of a generalized curve has this normal form.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ArithmeticOneGonParameter
variable {R : Type} [CommRing R] (I : Ideal R) (hI : IsNilpotent I)
  (f : ParameterRing →+* R ⧸ I)

include hI in
/-- The open condition lifts along every prescribed lift of the degeneration parameter. -/
theorem lifted_factor_isUnit (t : R) (ht : Ideal.Quotient.mk I t = f parameter) :
    IsUnit (1 + 432 * t) := by
  apply hI.isUnit_quotient_mk_iff.mp
  simpa only [map_add, map_one, map_mul, map_ofNat, ht] using hom_factor_isUnit f

include hI in
/-- Every chosen parameter lift produces a homomorphism lifting the entire original test. -/
theorem exists_prescribed_nilpotent_lift (t : R)
    (ht : Ideal.Quotient.mk I t = f parameter) :
    ∃ g : ParameterRing →+* R, (Ideal.Quotient.mk I).comp g = f ∧ g parameter = t := by
  let g := specialize t (lifted_factor_isUnit I hI f t ht)
  refine ⟨g, ?_, specialize_parameter _ _⟩
  apply hom_ext
  change Ideal.Quotient.mk I (g parameter) = f parameter
  rw [specialize_parameter]
  exact ht

include hI in
/-- Every infinitesimal parameter test admits an actual integral-ring lift. -/
theorem exists_nilpotent_lift :
    ∃ g : ParameterRing →+* R, (Ideal.Quotient.mk I).comp g = f := by
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (f parameter)
  obtain ⟨g, hg, _⟩ := exists_prescribed_nilpotent_lift I hI f t ht
  exact ⟨g, hg⟩

end FLT.Mazur.ArithmeticOneGonParameter
