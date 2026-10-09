/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFiberConic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The scheme-theoretic conic component

The quotient of the full fiber by its conic factor is the actual conic
coordinate algebra. No radical, reducedness or pointwise replacement is used.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassModificationX

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (a c : R)

/-- The original equation cutting out the conic component of the full fiber. -/
def fiberConicIdeal : Ideal (FiberCoordinate a c) := Ideal.span {fiberConicFactor a c}

/-- The conic equation vanishes in its actual fiber quotient. -/
theorem conic_quotient_relation :
    Ideal.Quotient.mk (fiberConicIdeal a c) (fiberV a c) *
        (Ideal.Quotient.mk (fiberConicIdeal a c) (fiberV a c) + algebraMap R _ a) -
      algebraMap R _ c * Ideal.Quotient.mk (fiberConicIdeal a c) (fiberT a c) ^ 2 = 0 := by
  have h : Ideal.Quotient.mk (fiberConicIdeal a c) (fiberConicFactor a c) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  simpa only [fiberConicFactor, map_sub, map_mul, map_add, map_pow,
    Ideal.Quotient.mk_algebraMap] using h

/-- The conic maps back to the actual quotient using its original coordinates. -/
def conicQuotientBackward : ConicCoordinate a c →ₐ[R]
    FiberCoordinate a c ⧸ fiberConicIdeal a c :=
  conicEvaluation a c (Ideal.Quotient.mk _ (fiberT a c))
    (Ideal.Quotient.mk _ (fiberV a c)) (conic_quotient_relation a c)

/-- The conic map kills its original principal ideal. -/
theorem fiberConicIdeal_le_ker : fiberConicIdeal a c ≤ RingHom.ker (fiberConicMap a c) := by
  rw [fiberConicIdeal, Ideal.span_le, Set.singleton_subset_iff]
  exact fiberConicMap_factor a c

/-- The actual factor map from the conic quotient. -/
def conicQuotientForward : (FiberCoordinate a c ⧸ fiberConicIdeal a c) →ₐ[R]
    ConicCoordinate a c :=
  Ideal.Quotient.liftₐ _ (fiberConicMap a c) (fun _ hz ↦ fiberConicIdeal_le_ker a c hz)

/-- The forward quotient map agrees with the original conic restriction. -/
@[simp] theorem conicQuotientForward_mk (z : FiberCoordinate a c) :
    conicQuotientForward a c (Ideal.Quotient.mk _ z) = fiberConicMap a c z := rfl

/-- The quotient inverse preserves the incidence coordinate. -/
@[simp] theorem conicQuotientBackward_t : conicQuotientBackward a c (conicT a c) =
    Ideal.Quotient.mk _ (fiberT a c) := conicEvaluation_t _ _ _ _ _

/-- The quotient inverse preserves the slope. -/
@[simp] theorem conicQuotientBackward_v : conicQuotientBackward a c (conicV a c) =
    Ideal.Quotient.mk _ (fiberV a c) := conicEvaluation_v _ _ _ _ _

/-- The two substitutions recover the original quotient map on every fiber function. -/
theorem conicQuotientBackward_comp :
    (conicQuotientBackward a c).comp (fiberConicMap a c) =
      Ideal.Quotient.mkₐ R (fiberConicIdeal a c) := by
  apply fiber_hom_ext <;>
    simp only [AlgHom.comp_apply, fiberConicMap_t, fiberConicMap_v,
      conicQuotientBackward_t, conicQuotientBackward_v, Ideal.Quotient.mkₐ_eq_mk]

/-- The conic is exactly the scheme-theoretic quotient by its original factor. -/
def conicQuotientEquiv :
    (FiberCoordinate a c ⧸ fiberConicIdeal a c) ≃ₐ[R] ConicCoordinate a c := by
  apply AlgEquiv.ofAlgHom (conicQuotientForward a c) (conicQuotientBackward a c)
  · apply conic_hom_ext <;>
      simp only [AlgHom.comp_apply, conicQuotientBackward_t, conicQuotientBackward_v,
        conicQuotientForward_mk, fiberConicMap_t, fiberConicMap_v, AlgHom.id_apply]
  · apply AlgHom.ext
    intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact DFunLike.congr_fun (conicQuotientBackward_comp a c) z

/-- The conic quotient isomorphism is induced by the original map. -/
@[simp] theorem conicQuotientEquiv_mk (z : FiberCoordinate a c) :
    conicQuotientEquiv a c (Ideal.Quotient.mk _ z) = fiberConicMap a c z := rfl

/-- The conic map is surjective on actual coordinate algebras. -/
theorem fiberConicMap_surjective : Function.Surjective (fiberConicMap a c) := by
  intro z
  obtain ⟨q, hq⟩ := (conicQuotientEquiv a c).surjective z
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨w, hq⟩

/-- The complete kernel of conic restriction is the original principal conic ideal. -/
theorem fiberConicMap_ker : RingHom.ker (fiberConicMap a c) = fiberConicIdeal a c := by
  refine le_antisymm ?_ (fiberConicIdeal_le_ker a c)
  intro z hz
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply (conicQuotientEquiv a c).injective
  have hz' : fiberConicMap a c z = 0 := hz
  simpa only [conicQuotientEquiv_mk, map_zero] using hz'

end FLT.Mazur.WeierstrassModificationX
