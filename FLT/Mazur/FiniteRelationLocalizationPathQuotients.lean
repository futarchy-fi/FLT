/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationLocalizationOverlapQuotients
public import FLT.Mazur.LocalizedKernelPathCompatibility

/-!
# Shared finite quotients from localized restriction paths

Commuting restriction paths into genuine localized targets prove the kernel
compatibility required for exact ideal patching. All finite quotient targets
remain fixed while a single ambient source relation set is refined.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteRelationLocalization

universe u v w z z' t

variable (R : Type u) [CommRing R] {P : Type v} [CommRing P] [Algebra R P]
  [Algebra.FinitePresentation R P] (I : Ideal P)
  {ι : Type w} [Finite ι] (r : ι → P)
  {A : ι → Type z'} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FinitePresentation R (A i)]

/-- Actual localized paths suffice for simultaneous exact quotient realization. -/
theorem exists_shared_quotient_equivs_of_paths (s : Finset I)
    (f : ∀ i, Stage I (r i) s →ₐ[R] A i) (hf : ∀ i, Function.Surjective (f i))
    (hkill : ∀ i, RingHom.ker (f i).toRingHom ≤
      RingHom.ker (toQuotient R I (r i) s).toRingHom)
    (U : ι → ι → Type z) [∀ i j, CommRing (U i j)]
    [∀ i j, Algebra (Stage I (r j) s) (U i j)]
    [∀ i j, IsLocalization.Away (numerator I (r j) s (r i)) (U i j)]
    (V : ι → ι → Type t) [∀ i j, CommRing (V i j)]
    [∀ i j, Algebra (A j) (V i j)]
    [∀ i j, IsLocalization.Away (f j (numerator I (r j) s (r i))) (V i j)]
    (a : ∀ i j, Stage I (r i) s →+* U i j) (b : ∀ i j, A i →+* V i j)
    (ha : ∀ i j, (a i j).comp (numerator I (r i) s) =
      (algebraMap (Stage I (r j) s) (U i j)).comp (numerator I (r j) s))
    (hp : ∀ i j, (LocalizedKernelComparison.comparison (U := U i j) (V := V i j)
      (numerator I (r j) s (r i)) (f j).toRingHom).comp (a i j) =
        (b i j).comp (f i).toRingHom) :
    ∃ (q : Finset I) (hsq : s ≤ q) (e : ∀ i, Stage I (r i) q ≃ₐ[R] A i),
      ∀ i, (e i).toAlgHom.comp (transition R I (r i) hsq) = f i := by
  apply exists_shared_quotient_equivs R I r s f hf hkill
  intro i j x hx
  exact LocalizedKernelComparison.exists_pow_mul_eq_zero_of_paths (r i) x.val
    (numerator I (r i) s) (numerator I (r j) s) (f i).toRingHom (f j).toRingHom
    (a i j) (b i j) (ha i j) (hp i j) hx

end FLT.Mazur.FiniteRelationLocalization
