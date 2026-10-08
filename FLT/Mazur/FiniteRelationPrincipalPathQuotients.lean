/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationLocalizationOverlapQuotients
public import FLT.Mazur.PrincipalLocalizedKernelPaths

/-!
# Exact shared quotients with canonical overlap rings

Only the finite target restriction maps and their equations on the ambient
stage are supplied. The source overlap rings and quotient comparisons are
constructed as actual localizations, and their kernel compatibility is
proved before patching one common ambient relation set.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteRelationLocalization

universe u v w z

variable (R : Type u) [CommRing R] {P : Type v} [CommRing P] [Algebra R P]
  [Algebra.FinitePresentation R P] (I : Ideal P)
  {ι : Type w} [Finite ι] (r : ι → P)
  {A : ι → Type z} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FinitePresentation R (A i)]

/-- Ambient equations into canonical localized targets give exact shared finite quotients. -/
theorem exists_shared_quotient_equivs_of_principal_paths (s : Finset I)
    (f : ∀ i, Stage I (r i) s →ₐ[R] A i) (hf : ∀ i, Function.Surjective (f i))
    (hkill : ∀ i, RingHom.ker (f i).toRingHom ≤
      RingHom.ker (toQuotient R I (r i) s).toRingHom)
    (b : ∀ i j, A i →+* Localization.Away (f j (numerator I (r j) s (r i))))
    (hp : ∀ i j, ((b i j).comp (f i).toRingHom).comp
        (algebraMap (FiniteRelationModel.Stage I s) (Stage I (r i) s)) =
      ((algebraMap (A j) (Localization.Away (f j (numerator I (r j) s (r i))))).comp
        (f j).toRingHom).comp
          (algebraMap (FiniteRelationModel.Stage I s) (Stage I (r j) s))) :
    ∃ (q : Finset I) (hsq : s ≤ q) (e : ∀ i, Stage I (r i) q ≃ₐ[R] A i),
      ∀ i, (e i).toAlgHom.comp (transition R I (r i) hsq) = f i := by
  apply exists_shared_quotient_equivs R I r s f hf hkill
  intro i j x hx
  obtain ⟨n, hn⟩ := PrincipalLocalizedKernelPaths.exists_pow_mul_eq_zero
    (Ideal.Quotient.mk (FiniteRelationModel.relations I s) (r i))
    (Ideal.Quotient.mk (FiniteRelationModel.relations I s) (r j))
    (f j).toRingHom (f i).toRingHom (b i j) (hp i j)
    (Ideal.Quotient.mk (FiniteRelationModel.relations I s) x.val) hx
  change f j (algebraMap (FiniteRelationModel.Stage I s) (Stage I (r j) s)
    (Ideal.Quotient.mk _ (r i) ^ n * Ideal.Quotient.mk _ x.val)) = 0 at hn
  refine ⟨n, ?_⟩
  simpa only [numerator, RingHom.comp_apply, map_mul, map_pow] using hn

end FLT.Mazur.FiniteRelationLocalization
