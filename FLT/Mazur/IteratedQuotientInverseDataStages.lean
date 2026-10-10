/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IteratedPolynomialDataStages
public import FLT.Mazur.IteratedQuotientAlgebra

/-!
# Shared quotient arrows with inverse representatives in the coefficient ring

Construct both levels of arrows at shared ambient stages, with the actual
inverse representatives included in the coefficient ring together with the
arrows, denominators and equations. Extra finite equations are retained.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FinitePolynomialCoefficients

universe u v w z t e h

variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
  (n : ι → ℕ) (r : ∀ i, MvPolynomial (Fin (n i)) R)
  {J : ι → Type w} [∀ i, Finite (J i)]
  (s : ∀ i, J i → Localization.Away (r i))
  (I : ∀ i, Ideal (MvPolynomial (Fin (n i)) R))
  {K : ι → Type z} [∀ i, Finite (K i)]
  {L : ∀ i, J i → Type t} [∀ i j, Finite (L i j)]
  {E : ι → ι → Type e} [∀ i j, Finite (E i j)]
  {H : ∀ (_ : ι) j, J j → Type h} [∀ i j k, Finite (H i j k)]

/-- Build both arrow levels at shared stages, retaining extra finite equations. -/
theorem exists_iterated_stages_with_inverse_data
    (f : ∀ i j, E i j → MvPolynomial (Fin (n i)) R →ₐ[R] Localization.Away (r j))
    (g : ∀ i j k, H i j k →
      MvPolynomial (Fin (n i)) R →ₐ[R] Localization.Away (s j k))
    (hf : ∀ i j a, I i ≤ ((I j).map (algebraMap _ (Localization.Away (r j)))).comap
      (f i j a).toRingHom)
    (hg : ∀ i j k a, I i ≤ (((I j).map (algebraMap _ (Localization.Away (r j)))).map
      (algebraMap _ (Localization.Away (s j k)))).comap (g i j k a).toRingHom)
    (v : ∀ i j, E i j → Localization.Away (r j))
    (hv : ∀ i j a, f i j a (r i) * v i j a - 1 ∈
      (I j).map (algebraMap _ (Localization.Away (r j))))
    (w : ∀ i j k, H i j k → Localization.Away (s j k))
    (hw : ∀ i j k a, g i j k a (r i) * w i j k a - 1 ∈
      ((I j).map (algebraMap _ (Localization.Away (r j)))).map
        (algebraMap _ (Localization.Away (s j k))))
    (b : ∀ i, Finset (I i))
    (x : ∀ i, K i → Localization.Away (r i))
    (hx : ∀ i k, x i k ∈ (I i).map (algebraMap _ (Localization.Away (r i))))
    (y : ∀ i j, L i j → Localization.Away (s i j))
    (hy : ∀ i j k, y i j k ∈ ((I i).map (algebraMap _ (Localization.Away (r i)))).map
      (algebraMap _ (Localization.Away (s i j)))) :
    ∃ t : ∀ i, Finset (I i), b ≤ t ∧
      ∃ (F : ∀ i j, E i j →
          PrincipalQuotientProjection.Target (FiniteRelationModel.relations (I i) (t i)) (r i)
            →ₐ[R]
          PrincipalQuotientProjection.Target (FiniteRelationModel.relations (I j) (t j)) (r j))
        (G : ∀ i j k, H i j k →
          PrincipalQuotientProjection.Target (FiniteRelationModel.relations (I i) (t i)) (r i)
            →ₐ[R]
          IteratedQuotientProjection.Target
            (FiniteRelationModel.relations (I j) (t j)) (r j) (s j k)),
        (∀ i j a p, F i j a (algebraMap _ _
          (Ideal.Quotient.mk (FiniteRelationModel.relations (I i) (t i)) p)) =
          PrincipalQuotientProjection.projection
            (FiniteRelationModel.relations (I j) (t j)) (r j) (f i j a p)) ∧
        (∀ i j k a p, G i j k a (algebraMap _ _
          (Ideal.Quotient.mk (FiniteRelationModel.relations (I i) (t i)) p)) =
          IteratedQuotientProjection.projection
            (FiniteRelationModel.relations (I j) (t j)) (r j) (s j k) (g i j k a p)) ∧
        (∀ i k, x i k ∈ (FiniteRelationModel.relations (I i) (t i)).map
          (algebraMap _ (Localization.Away (r i)))) ∧
        ∀ i j k, y i j k ∈ ((FiniteRelationModel.relations (I i) (t i)).map
          (algebraMap _ (Localization.Away (r i)))).map
            (algebraMap _ (Localization.Away (s i j))) := by
  classical
  let _ := Fintype.ofFinite ι
  let _ (i j) := Fintype.ofFinite (E i j)
  let _ (i j k) := Fintype.ofFinite (H i j k)
  let _ (i) := Fintype.ofFinite (K i)
  let _ (i j) := Fintype.ofFinite (L i j)
  let T (j) := (Σ i, E i j) ⊕ K j
  let U (j) (k : J j) := (Σ i, H i j k) ⊕ L j k
  let _ (j) : Fintype (T j) := inferInstanceAs (Fintype ((Σ i, E i j) ⊕ K j))
  let _ (j k) : Fintype (U j k) := inferInstanceAs (Fintype ((Σ i, H i j k) ⊕ L j k))
  let x' : ∀ j, T j → Localization.Away (r j) := fun j a ↦ match a with
    | .inl ⟨i, a⟩ => f i j a (r i) * v i j a - 1
    | .inr k => x j k
  let y' : ∀ j k, U j k → Localization.Away (s j k) := fun j k a ↦ match a with
    | .inl ⟨i, a⟩ => g i j k a (r i) * w i j k a - 1
    | .inr l => y j k l
  have hx' (j) (a : T j) : x' j a ∈ (I j).map
      (algebraMap _ (Localization.Away (r j))) := by
    rcases a with ⟨i, a⟩ | k
    · exact hv i j a
    · exact hx j k
  have hy' (j k) (a : U j k) : y' j k a ∈
      ((I j).map (algebraMap _ (Localization.Away (r j)))).map
        (algebraMap _ (Localization.Away (s j k))) := by
    rcases a with ⟨i, a⟩ | l
    · exact hw i j k a
    · exact hy j k l
  let v' (j) (a : Σ i, E i j) := v a.1 j a.2
  let w' (j k) (a : Σ i, H i j k) := w a.1 j k a.2
  obtain ⟨t, ht, hft, hgt, hxt, hyt⟩ :=
    exists_iterated_stable_stages_with_data n r s f g I hf hg v' w' b x' hx' y' hy'
  let F (i j) (a : E i j) := PrincipalQuotientProjection.principalArrowAlgHom R
    (FiniteRelationModel.relations (I j) (t j)) (r j)
    (FiniteRelationModel.relations (I i) (t i)) (r i)
    (f i j a) (hft i j a) (v i j a) (hxt j (.inl ⟨i, a⟩))
  let G (i j k) (a : H i j k) := IteratedQuotientProjection.principalArrowAlgHom R
    (FiniteRelationModel.relations (I j) (t j)) (r j) (s j k)
    (FiniteRelationModel.relations (I i) (t i)) (r i)
    (g i j k a) (hgt i j k a) (w i j k a) (hyt j k (.inl ⟨i, a⟩))
  exact ⟨t, ht, F, G,
    fun i j a p ↦ PrincipalQuotientProjection.principalArrowAlgHom_numerator R
      _ _ _ _ _ _ _ _ p,
    fun i j k a p ↦ IteratedQuotientProjection.principalArrowAlgHom_numerator R
      _ _ _ _ _ _ _ _ _ p,
    fun i k ↦ hxt i (.inr k), fun i j k ↦ hyt i j (.inr k)⟩

end FLT.Mazur.FinitePolynomialCoefficients
