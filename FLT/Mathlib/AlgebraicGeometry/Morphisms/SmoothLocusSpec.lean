/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mathlib.RingTheory.Smooth.FiberLocalization
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# The smooth locus on spectra

The scheme smooth locus agrees with the algebraic smooth locus over any
commutative base ring. For a flat finitely presented algebra, this identifies
the relative smooth locus pointwise on each algebraic fibre.
-/

public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- A finitely presented algebra gives a locally finitely presented spectrum map. -/
instance Spec.algebraMap_locallyOfFinitePresentation [Algebra.FinitePresentation R S] :
    LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
  change (algebraMap R S).FinitePresentation
  rw [RingHom.finitePresentation_algebraMap]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The stalk definition of the smooth locus on spectra agrees with the
algebraic definition, without a field hypothesis on the base. -/
theorem Spec.mem_smoothLocus_iff (q : PrimeSpectrum S)
    [LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R S)))] :
    q ∈ (Spec.map (CommRingCat.ofHom (algebraMap R S))).smoothLocus ↔
      Algebra.IsSmoothAt R q.asIdeal := by
  let p := q.asIdeal.under R
  let := Localization.AtPrime.algebraOfLiesOver p q.asIdeal
  rw [Scheme.Hom.mem_smoothLocus,
    RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff
      (Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom (algebraMap R S)) q)]
  change Algebra.FormallySmooth (Localization.AtPrime p) (Localization.AtPrime q.asIdeal) ↔ _
  exact Algebra.FormallySmooth.iff_restrictScalars.symm

/-- The inverse image of the relative smooth locus in an algebraic fibre is
exactly the smooth locus of that fibre. -/
theorem Spec.mem_smoothLocus_fiber_iff [Algebra.FinitePresentation R S] [Module.Flat R S]
    (p : Ideal R) [p.IsPrime] (q : PrimeSpectrum (p.Fiber S)) :
    PrimeSpectrum.comap Algebra.TensorProduct.includeRight.toRingHom q ∈
        (Spec.map (CommRingCat.ofHom (algebraMap R S))).smoothLocus ↔
      q ∈ (Spec.map (CommRingCat.ofHom
        (algebraMap p.ResidueField (p.Fiber S)))).smoothLocus := by
  rw [Spec.mem_smoothLocus_iff, Spec.mem_smoothLocus_iff]
  exact Algebra.isSmoothAt_iff_isSmoothAt_fiber p q.asIdeal

end AlgebraicGeometry
