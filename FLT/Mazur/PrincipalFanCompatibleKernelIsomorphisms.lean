/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalFanStages
public import FLT.Mazur.FiniteRelationLocalizationOverlapQuotients

/-!
# Shared chart isomorphisms retaining all overlap targets

Surjective coordinate lifts of original injections become isomorphisms with
one common ambient source refinement and every target unchanged, provided
their kernels agree on principal overlaps. Exact ideal patching is essential:
an arbitrary union of source relations need not preserve the target quotients.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Algebra.FiniteType R A] {ι : Type v} [Finite ι]
  {B : ι → Type u} [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
  [∀ i, Algebra.FiniteType R (B i)]
  {a : ι → A} {b : ∀ i, B i}
  {f : ∀ i, Localization.Away (a i) →ₐ[R] Localization.Away (b i)}

/-- Compatible kernels let all outgoing isomorphisms share source relations and fixed targets. -/
theorem exists_principalFan_bijective_of_compatible_kernels
    (hf : ∀ i, Function.Injective (f i)) (x : PrincipalFanStage a b f)
    (hx : ∀ i, Function.Surjective (x.hom i))
    (hcompat : ∀ i j, ∀ z : relationIdeal R A,
      x.hom i (FiniteRelationLocalization.numerator (relationIdeal R A)
        (principalRepresentative R A (a i)) x.source z) = 0 →
      ∃ n : ℕ, x.hom j (FiniteRelationLocalization.numerator (relationIdeal R A)
        (principalRepresentative R A (a j)) x.source
          (principalRepresentative R A (a i) ^ n * z.val)) = 0) :
    ∃ y : PrincipalFanStage a b f, x ≤ y ∧ y.target = x.target ∧
      ∀ i, Function.Bijective (y.hom i) := by
  have hk (i) : RingHom.ker (x.hom i).toRingHom ≤
      RingHom.ker (FiniteRelationLocalization.toQuotient R (relationIdeal R A)
        (principalRepresentative R A (a i)) x.source).toRingHom := by
    intro z hz
    change x.hom i z = 0 at hz
    apply (principalQuotientEquiv R A (a i)).injective
    change principalStageMap R A (a i) x.source z = principalQuotientEquiv R A (a i) 0
    rw [map_zero]
    apply hf i
    rw [← AlgHom.comp_apply, ← x.fac i, AlgHom.comp_apply, hz, map_zero, map_zero]
  obtain ⟨t, hst, e, he⟩ := FiniteRelationLocalization.exists_shared_quotient_equivs R
    (relationIdeal R A) (fun i ↦ principalRepresentative R A (a i)) x.source x.hom hx hk hcompat
  have hfac (i) : (principalStageMap R (B i) (b i) (x.target i)).comp (e i).toAlgHom =
      (f i).comp (principalStageMap R A (a i) t) := by
    apply (AlgHom.cancel_right (FiniteRelationLocalization.transition_surjective R
      (relationIdeal R A) (principalRepresentative R A (a i)) hst)).mp
    rw [AlgHom.comp_assoc, he, x.fac, AlgHom.comp_assoc, principalStageMap_transition]
  let y : PrincipalFanStage a b f := ⟨t, x.target, fun i ↦ (e i).toAlgHom, hfac⟩
  refine ⟨y, ⟨hst, fun i ↦ ⟨hst, le_rfl, ?_⟩⟩, rfl, fun i ↦ (e i).bijective⟩
  change (e i).toAlgHom.comp (principalTransition (a i) hst) =
    (principalTransition (b i) (le_refl (x.target i))).comp (x.hom i)
  rw [principalTransition_refl, AlgHom.id_comp]
  exact he i

end FLT.Mazur.FiniteTypeRelationModel
