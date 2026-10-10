/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationLocalizationSharedIdeals
public import FLT.Mazur.LocalizedIdealOverlapMembership
public import FLT.Mazur.SurjectiveAlgHomKernelEquiv

/-!
# Shared quotient isomorphisms from compatible overlap ideals

Inclusion of ideals on genuine localized pairwise intersections supplies the
compatibility needed for exact shared kernels. Surjective maps to finitely
presented targets with these kernels therefore become isomorphisms at one
ambient stage, retaining every target and every chosen quotient map.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteRelationLocalization

universe u v w z z'

variable (R : Type u) [CommRing R] {P : Type v} [CommRing P] [Algebra R P]
  (I : Ideal P) {ι : Type w} [Finite ι] (r : ι → P)

/-- Actual ideal compatibility on localized overlaps gives exact shared transition kernels. -/
theorem exists_shared_transition_ker_eq_of_overlaps (s : Finset I)
    (J : ∀ i, Ideal (Stage I (r i) s)) (hJ : ∀ i, (J i).FG)
    (hkill : ∀ i, J i ≤ RingHom.ker (toQuotient R I (r i) s).toRingHom)
    (U : ι → ι → Type z) [∀ i j, CommRing (U i j)]
    [∀ i j, Algebra (Stage I (r j) s) (U i j)]
    [∀ i j, IsLocalization.Away (numerator I (r j) s (r i)) (U i j)]
    (f : ∀ i j, Stage I (r i) s →+* U i j)
    (hcomm : ∀ i j, (f i j).comp (numerator I (r i) s) =
      (algebraMap (Stage I (r j) s) (U i j)).comp (numerator I (r j) s))
    (hcompat : ∀ i j, (J i).map (f i j) ≤
      (J j).map (algebraMap (Stage I (r j) s) (U i j))) :
    ∃ (t : Finset I) (hst : s ≤ t),
      ∀ i, RingHom.ker (transition R I (r i) hst).toRingHom = J i := by
  apply exists_shared_transition_ker_eq R I r s J hJ hkill
  intro i j z hz
  exact PrincipalIdealPatching.exists_pow_mul_mem_of_overlap (r i) z
    (numerator I (r i) s) (numerator I (r j) s) (f i j) (hcomm i j)
    (J i) (J j) (hcompat i j) hz

variable [Algebra.FinitePresentation R P]
  {A : ι → Type z'} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FinitePresentation R (A i)]

/-- Compatible finite quotients on distinct principal opens share one ambient model exactly. -/
theorem exists_shared_quotient_equivs (s : Finset I)
    (f : ∀ i, Stage I (r i) s →ₐ[R] A i) (hf : ∀ i, Function.Surjective (f i))
    (hkill : ∀ i, RingHom.ker (f i).toRingHom ≤
      RingHom.ker (toQuotient R I (r i) s).toRingHom)
    (hcompat : ∀ i j, ∀ z : I, f i (numerator I (r i) s z) = 0 →
      ∃ n : ℕ, f j (numerator I (r j) s (r i ^ n * (z : P))) = 0) :
    ∃ (t : Finset I) (hst : s ≤ t) (e : ∀ i, Stage I (r i) t ≃ₐ[R] A i),
      ∀ i, (e i).toAlgHom.comp (transition R I (r i) hst) = f i := by
  obtain ⟨t, hst, ht⟩ := exists_shared_transition_ker_eq R I r s
    (fun i ↦ RingHom.ker (f i).toRingHom)
    (fun i ↦ Algebra.FinitePresentation.ker_fG_of_surjective (f i) (hf i)) hkill hcompat
  choose e he using fun i ↦ exists_algEquiv_of_ker_eq (transition R I (r i) hst)
    (f i) (transition_surjective R I (r i) hst) (hf i) (ht i)
  exact ⟨t, hst, e, he⟩

end FLT.Mazur.FiniteRelationLocalization
