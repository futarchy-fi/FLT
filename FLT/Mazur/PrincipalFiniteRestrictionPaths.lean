/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationIteratedRestrictionPaths
public import FLT.Mazur.PrincipalOriginalRestrictionPaths

/-!
# Finite restrictions constructed from original chart coordinates

The input gives original principal chart isomorphisms and their presentation
squares. The restriction maps themselves are constructed, then descended with
all ambient equations to explicit double localizations at one relation stage.
The source presentation rings remain fixed in this construction.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PrincipalOriginalRestrictionPaths

universe u v w z

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
  {B : Type w} [CommRing B] [Algebra R B]
  {D : Type z} [CommRing D] [Algebra R D]

/-- A prescribed image denominator gives an actual original restriction and its square. -/
theorem exists_restriction_at (r : A) (e : Localization.Away r ≃ₐ[R] B)
    (f : A →ₐ[R] D) (z : D) (hz : f r = z) :
    ∃ ρ : B →ₐ[R] Localization.Away z,
      ρ.comp (e.toAlgHom.comp (Algebra.algHom R A (Localization.Away r))) =
        (Algebra.algHom R D (Localization.Away z)).comp f := by
  subst z
  exact ⟨restriction r e f, by rw [← AlgHom.comp_assoc, restriction_ambient]⟩

end FLT.Mazur.PrincipalOriginalRestrictionPaths

namespace FLT.Mazur.FiniteRelationIterated

universe u v w z w' z'

variable {R : Type u} [CommRing R] {P : Type v} [CommRing P] [Algebra R P]
  (I : Ideal P) (r : P) (s : Finset I)
  {ι : Type z} [Finite ι] (d : ι → FiniteRelationLocalization.Stage I r s)

/-- Construct finite restriction maps from original isomorphisms, preserving ambient squares. -/
theorem exists_restrictions_of_coordinates
    (A B : ι → Type w) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    (a : ∀ i, A i) (e : ∀ i, Localization.Away (a i) ≃ₐ[R] B i)
    (f : ∀ i, A i →ₐ[R] FiniteRelationLocalization.Quotient I r)
    (hd : ∀ i, f i (a i) = FiniteRelationLocalization.toQuotient R I r s (d i))
    (T : ι → Type w') [∀ i, CommRing (T i)] [∀ i, Algebra R (T i)]
    [∀ i, Algebra.FinitePresentation R (T i)]
    (C : ι → Type z') [∀ i, CommRing (C i)] [∀ i, Algebra R (C i)]
    [∀ i, Algebra.FiniteType R (C i)]
    (t : Set.Ici s) (p : ∀ i, C i →ₐ[R] A i) (q : ∀ i, T i →ₐ[R] B i)
    (l : ∀ i, C i →ₐ[R] T i)
    (b : ∀ i, C i →ₐ[R] FiniteRelationLocalization.Stage I r t.val)
    (hl : ∀ i, (q i).comp (l i) = ((e i).toAlgHom.comp
      (Algebra.algHom R (A i) (Localization.Away (a i)))).comp (p i))
    (hb : ∀ i, (FiniteRelationLocalization.toQuotient R I r t.val).comp (b i) =
      (f i).comp (p i)) :
    ∃ (k : Set.Ici s) (htk : t ≤ k),
      ∃ ρ : ∀ i, T i →ₐ[R] Stage R I r s (d i) k,
        ∀ i, (ρ i).comp (l i) =
          (Algebra.algHom R (FiniteRelationLocalization.Stage I r k.val)
            (Stage R I r s (d i) k)).comp
              ((FiniteRelationLocalization.transition R I r htk).comp (b i)) := by
  choose g hg using fun i ↦ PrincipalOriginalRestrictionPaths.exists_restriction_at
    (a i) (e i) (f i) (FiniteRelationLocalization.toQuotient R I r s (d i)) (hd i)
  let b' (i) := (Algebra.algHom R (FiniteRelationLocalization.Stage I r t.val)
    (Stage R I r s (d i) t)).comp (b i)
  have he (i) : ((g i).comp (q i)).comp (l i) =
      (toQuotient R I r s (d i) t).comp (b' i) := by
    rw [AlgHom.comp_assoc, hl, ← AlgHom.comp_assoc, hg]
    apply AlgHom.ext
    intro x
    have h := AlgHom.congr_fun (hb i) x
    change algebraMap _ (Quotient R I r s (d i)) (f i (p i x)) =
      toQuotient R I r s (d i) t (algebraMap _ (Stage R I r s (d i) t) (b i x))
    rw [toQuotient_algebraMap]
    exact congrArg (algebraMap _ (Quotient R I r s (d i))) h.symm
  obtain ⟨k, htk, ρ, _, hρ⟩ := exists_restriction_paths I r s d T C t l b'
    (fun i ↦ (g i).comp (q i)) he
  refine ⟨k, htk, ρ, fun i ↦ ?_⟩
  rw [hρ]
  apply AlgHom.ext
  intro x
  exact transition_algebraMap R I r s (d i) htk (b i x)

end FLT.Mazur.FiniteRelationIterated
