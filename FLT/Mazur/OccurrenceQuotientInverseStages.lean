/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OccurrencePolynomialDataStages
public import FLT.Mazur.IteratedQuotientAlgebra

/-!
# Shared quotient arrows with inverse representatives in the coefficient ring

Construct both levels of arrows at shared ambient stages, with the actual
inverse representatives included in the coefficient ring together with the
arrows, denominators and equations. Extra finite equations are retained.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FinitePolynomialCoefficients

universe u v w z t e h q

variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
  (n : ι → ℕ) {O : ι → Type q} [∀ i, Finite (O i)]
  (r : ∀ i, O i → MvPolynomial (Fin (n i)) R)
  {J : ∀ i, O i → Type w} [∀ i o, Finite (J i o)]
  (s : ∀ i o, J i o → Localization.Away (r i o))
  (I : ∀ i, Ideal (MvPolynomial (Fin (n i)) R))
  {K : ∀ i, O i → Type z} [∀ i o, Finite (K i o)]
  {L : ∀ i o, J i o → Type t} [∀ i o j, Finite (L i o j)]
  {E : ∀ (_ : ι) j, O j → Type e} [∀ i j o, Finite (E i j o)]
  {H : ∀ (_ : ι) j o, J j o → Type h} [∀ i j o k, Finite (H i j o k)]
  (src : ∀ i j o, E i j o → O i)
  (src₂ : ∀ i j o k, H i j o k → O i)

/-- Build both arrow levels at shared stages, retaining extra finite equations. -/
theorem exists_occurrence_stages_with_inverse_data
    (f : ∀ i j o, E i j o → MvPolynomial (Fin (n i)) R →ₐ[R] Localization.Away (r j o))
    (g : ∀ i j o k, H i j o k →
      MvPolynomial (Fin (n i)) R →ₐ[R] Localization.Away (s j o k))
    (hf : ∀ i j o a, I i ≤ ((I j).map (algebraMap _ (Localization.Away (r j o)))).comap
      (f i j o a).toRingHom)
    (hg : ∀ i j o k a, I i ≤ (((I j).map (algebraMap _ (Localization.Away (r j o)))).map
      (algebraMap _ (Localization.Away (s j o k)))).comap (g i j o k a).toRingHom)
    (v : ∀ i j o, E i j o → Localization.Away (r j o))
    (hv : ∀ i j o a, f i j o a (r i (src i j o a)) * v i j o a - 1 ∈
      (I j).map (algebraMap _ (Localization.Away (r j o))))
    (w : ∀ i j o k, H i j o k → Localization.Away (s j o k))
    (hw : ∀ i j o k a, g i j o k a (r i (src₂ i j o k a)) * w i j o k a - 1 ∈
      ((I j).map (algebraMap _ (Localization.Away (r j o)))).map
        (algebraMap _ (Localization.Away (s j o k))))
    (b : ∀ i, Finset (I i))
    (x : ∀ i o, K i o → Localization.Away (r i o))
    (hx : ∀ i o k, x i o k ∈ (I i).map (algebraMap _ (Localization.Away (r i o))))
    (y : ∀ i o j, L i o j → Localization.Away (s i o j))
    (hy : ∀ i o j k, y i o j k ∈ ((I i).map (algebraMap _ (Localization.Away (r i o)))).map
      (algebraMap _ (Localization.Away (s i o j)))) :
    ∃ t : ∀ i, Finset (I i), b ≤ t ∧
      ∃ (F : ∀ i j o (a : E i j o),
          PrincipalQuotientProjection.Target
            (FiniteRelationModel.relations (I i) (t i)) (r i (src i j o a))
            →ₐ[R]
          PrincipalQuotientProjection.Target (FiniteRelationModel.relations (I j) (t j)) (r j o))
        (G : ∀ i j o k (a : H i j o k),
          PrincipalQuotientProjection.Target
            (FiniteRelationModel.relations (I i) (t i)) (r i (src₂ i j o k a))
            →ₐ[R]
          IteratedQuotientProjection.Target
            (FiniteRelationModel.relations (I j) (t j)) (r j o) (s j o k)),
        (∀ i j o a p, F i j o a (algebraMap _ _
          (Ideal.Quotient.mk (FiniteRelationModel.relations (I i) (t i)) p)) =
          PrincipalQuotientProjection.projection
            (FiniteRelationModel.relations (I j) (t j)) (r j o) (f i j o a p)) ∧
        (∀ i j o k a p, G i j o k a (algebraMap _ _
          (Ideal.Quotient.mk (FiniteRelationModel.relations (I i) (t i)) p)) =
          IteratedQuotientProjection.projection
            (FiniteRelationModel.relations (I j) (t j)) (r j o) (s j o k) (g i j o k a p)) ∧
        (∀ i o k, x i o k ∈ (FiniteRelationModel.relations (I i) (t i)).map
          (algebraMap _ (Localization.Away (r i o)))) ∧
        ∀ i o j k, y i o j k ∈ ((FiniteRelationModel.relations (I i) (t i)).map
          (algebraMap _ (Localization.Away (r i o)))).map
            (algebraMap _ (Localization.Away (s i o j))) := by
  classical
  let _ := Fintype.ofFinite ι
  let _ (i j o) := Fintype.ofFinite (E i j o)
  let _ (i j o k) := Fintype.ofFinite (H i j o k)
  let _ (i o) := Fintype.ofFinite (K i o)
  let _ (i o j) := Fintype.ofFinite (L i o j)
  let T (j o) := (Σ i, E i j o) ⊕ K j o
  let U (j o) (k : J j o) := (Σ i, H i j o k) ⊕ L j o k
  let _ (j o) : Fintype (T j o) := inferInstanceAs (Fintype ((Σ i, E i j o) ⊕ K j o))
  let _ (j o k) : Fintype (U j o k) := inferInstanceAs (Fintype ((Σ i, H i j o k) ⊕ L j o k))
  let x' : ∀ j o, T j o → Localization.Away (r j o) := fun j o a ↦ match a with
    | .inl ⟨i, a⟩ => f i j o a (r i (src i j o a)) * v i j o a - 1
    | .inr k => x j o k
  let y' : ∀ j o k, U j o k → Localization.Away (s j o k) := fun j o k a ↦ match a with
    | .inl ⟨i, a⟩ => g i j o k a (r i (src₂ i j o k a)) * w i j o k a - 1
    | .inr l => y j o k l
  have hx' (j o) (a : T j o) : x' j o a ∈ (I j).map
      (algebraMap _ (Localization.Away (r j o))) := by
    rcases a with ⟨i, a⟩ | k
    · exact hv i j o a
    · exact hx j o k
  have hy' (j o k) (a : U j o k) : y' j o k a ∈
      ((I j).map (algebraMap _ (Localization.Away (r j o)))).map
        (algebraMap _ (Localization.Away (s j o k))) := by
    rcases a with ⟨i, a⟩ | l
    · exact hw i j o k a
    · exact hy j o k l
  let v' (j o) (a : Σ i, E i j o) := v a.1 j o a.2
  let w' (j o k) (a : Σ i, H i j o k) := w a.1 j o k a.2
  obtain ⟨t, ht, hft, hgt, hxt, hyt⟩ :=
    exists_occurrence_stable_stages_with_data n r s f g I hf hg v' w' b x' hx' y' hy'
  let F (i j o) (a : E i j o) := PrincipalQuotientProjection.principalArrowAlgHom R
    (FiniteRelationModel.relations (I j) (t j)) (r j o)
    (FiniteRelationModel.relations (I i) (t i)) (r i (src i j o a))
    (f i j o a) (hft i j o a) (v i j o a) (hxt j o (.inl ⟨i, a⟩))
  let G (i j o k) (a : H i j o k) := IteratedQuotientProjection.principalArrowAlgHom R
    (FiniteRelationModel.relations (I j) (t j)) (r j o) (s j o k)
    (FiniteRelationModel.relations (I i) (t i)) (r i (src₂ i j o k a))
    (g i j o k a) (hgt i j o k a) (w i j o k a) (hyt j o k (.inl ⟨i, a⟩))
  exact ⟨t, ht, F, G,
    fun i j o a p ↦ PrincipalQuotientProjection.principalArrowAlgHom_numerator R
      _ _ _ _ _ _ _ _ p,
    fun i j o k a p ↦ IteratedQuotientProjection.principalArrowAlgHom_numerator R
      _ _ _ _ _ _ _ _ _ p,
    fun i o k ↦ hxt i o (.inr k), fun i o j k ↦ hyt i o j (.inr k)⟩

end FLT.Mazur.FinitePolynomialCoefficients
