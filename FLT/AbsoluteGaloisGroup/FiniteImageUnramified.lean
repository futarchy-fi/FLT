/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.FiniteImageField
public import FLT.AbsoluteGaloisGroup.Unramified

/-!
# Arithmetic unramifiedness of a finite representation's kernel field

Triviality on the selected absolute inertia implies unramifiedness at every
prime above the place, for the exact field cut out by the representation.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace GaloisRepresentation.Extensions

variable {K H : Type*} [Field K] [NumberField K] [Group H]
  [TopologicalSpace H] [DiscreteTopology H]
  (f : Field.absoluteGaloisGroup K →ₜ* H)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))

/-- The local restriction kernel is precisely the pullback of the original kernel. -/
theorem finiteImageField_localRestriction_ker :
    (NumberField.InertiaComparison.localRestriction v
      (finiteImageField f).toIntermediateField).ker =
    f.toMonoidHom.ker.comap
      (Field.absoluteGaloisGroup.map (algebraMap K (v.adicCompletion K))).toMonoidHom := by
  rw [NumberField.InertiaComparison.localRestriction, ← MonoidHom.comap_ker,
    IntermediateField.restrictNormalHom_ker, finiteImageField_fixingSubgroup]

/-- Trivial absolute inertia gives arithmetic unramifiedness at all primes above `v`. -/
theorem finiteImageField_isUnramifiedIn
    (h : ∀ s ∈ localInertiaGroup v,
      f (Field.absoluteGaloisGroup.map (algebraMap K (v.adicCompletion K)) s) = 1) :
    Algebra.IsUnramifiedIn (NumberField.RingOfIntegers (finiteImageField f)) v.asIdeal := by
  apply NumberField.InertiaComparison.isUnramifiedIn_of_localInertia_le_ker
  rw [finiteImageField_localRestriction_ker]
  exact h

end GaloisRepresentation.Extensions
