/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFiberConicQuotient
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The incidence line and conic as actual closed subschemes

The full fiber is covered by the original incidence line and the conic.
Their scheme structures are retained over any coefficient ring and any c.
-/

@[expose] public noncomputable section

open Polynomial AlgebraicGeometry

namespace FLT.Mazur.WeierstrassModificationX

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (a c : R)

/-- The incidence map has exactly the original principal incidence ideal as its kernel. -/
theorem fiberIncidenceMap_ker : RingHom.ker (fiberIncidenceMap a c) =
    Ideal.span {fiberT a c} := by
  let I : Ideal (FiberCoordinate a c) := Ideal.span {fiberT a c}
  let g : R[X] →ₐ[R] FiberCoordinate a c ⧸ I :=
    aeval (Ideal.Quotient.mk I (fiberV a c))
  have ht : Ideal.Quotient.mk I (fiberT a c) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have he : g.comp (fiberIncidenceMap a c) = Ideal.Quotient.mkₐ R I := by
    apply fiber_hom_ext
    · simp only [AlgHom.comp_apply, fiberIncidenceMap_t, map_zero,
        Ideal.Quotient.mkₐ_eq_mk, ht]
    · simp only [AlgHom.comp_apply, fiberIncidenceMap_v, g, aeval_X,
        Ideal.Quotient.mkₐ_eq_mk]
  refine le_antisymm ?_ ?_
  · intro z hz
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hz' : fiberIncidenceMap a c z = 0 := hz
    have h := DFunLike.congr_fun he z
    simpa only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, hz', map_zero] using h.symm
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact fiberIncidenceMap_t a c

/-- Every polynomial slope function is the restriction of a full fiber function. -/
theorem fiberIncidenceMap_surjective : Function.Surjective (fiberIncidenceMap a c) := by
  intro p
  refine ⟨aeval (fiberV a c) p, ?_⟩
  rw [← aeval_algHom_apply, fiberIncidenceMap_v]
  exact aeval_X_left_apply p

/-- The actual incidence quotient is an affine line, also at middle depth. -/
def incidenceQuotientEquiv :
    (FiberCoordinate a c ⧸ Ideal.span {fiberT a c}) ≃ₐ[R] R[X] :=
  (Ideal.quotientEquivAlgOfEq R (fiberIncidenceMap_ker a c).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (fiberIncidenceMap_surjective a c))

/-- The incidence quotient comparison is the original restriction map. -/
@[simp] theorem incidenceQuotientEquiv_mk (z : FiberCoordinate a c) :
    incidenceQuotientEquiv a c (Ideal.Quotient.mk _ z) = fiberIncidenceMap a c z := by
  rw [incidenceQuotientEquiv, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk]
  exact Ideal.quotientKerAlgEquivOfSurjective_mk (fiberIncidenceMap_surjective a c) z

/-- The conic as a closed subscheme of the entire original fiber. -/
def fiberConicImmersion : Spec (.of (ConicCoordinate a c)) ⟶
    Spec (.of (FiberCoordinate a c)) :=
  Spec.map (CommRingCat.ofHom (fiberConicMap a c).toRingHom)

/-- The incidence line as a closed subscheme without dropping the conic term. -/
def fiberIncidenceImmersion : Spec (.of R[X]) ⟶ Spec (.of (FiberCoordinate a c)) :=
  Spec.map (CommRingCat.ofHom (fiberIncidenceMap a c).toRingHom)

instance fiberConicImmersion_isClosedImmersion : IsClosedImmersion (fiberConicImmersion a c) :=
  IsClosedImmersion.spec_of_surjective _ (fiberConicMap_surjective a c)

instance fiberIncidenceImmersion_isClosedImmersion :
    IsClosedImmersion (fiberIncidenceImmersion a c) :=
  IsClosedImmersion.spec_of_surjective _ (fiberIncidenceMap_surjective a c)

/-- The conic has precisely the support of the original conic factor. -/
theorem range_fiberConicImmersion : Set.range (fiberConicImmersion a c) =
    PrimeSpectrum.zeroLocus (fiberConicIdeal a c) := by
  rw [← fiberConicMap_ker]
  exact range_comap_of_surjective _ _ (fiberConicMap_surjective a c)

/-- The incidence line has precisely the original incidence-zero support. -/
theorem range_fiberIncidenceImmersion : Set.range (fiberIncidenceImmersion a c) =
    PrimeSpectrum.zeroLocus (Ideal.span {fiberT a c}) := by
  rw [← fiberIncidenceMap_ker]
  exact range_comap_of_surjective _ _ (fiberIncidenceMap_surjective a c)

/-- The actual incidence and conic closed subschemes cover the full fiber. -/
theorem fiber_incidence_conic_cover (p : Spec (.of (FiberCoordinate a c))) :
    p ∈ Set.range (fiberIncidenceImmersion a c) ∨ p ∈ Set.range (fiberConicImmersion a c) := by
  have h : fiberT a c * fiberConicFactor a c ∈ p.asIdeal := by
    rw [fiberConicFactor, fiber_relation]
    exact p.asIdeal.zero_mem
  rw [range_fiberIncidenceImmersion, range_fiberConicImmersion]
  rcases p.isPrime.mem_or_mem h with ht | hc
  · exact Or.inl (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ht))
  · exact Or.inr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hc))

end FLT.Mazur.WeierstrassModificationX
