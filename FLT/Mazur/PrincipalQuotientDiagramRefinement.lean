/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalQuotientDiagramStages

/-!
# Cofinal refinements retaining old principal-open arrow squares

Advance every vertex simultaneously, retaining both the original recovery maps
and every prescribed old arrow square. All targets remain the canonical
principal localizations of the shared ambient relation stages.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FinitePolynomialCoefficients

universe u v w

variable {R : Type u} [CommRing R]

/-- A principal stage transition commutes with projection from the unquotiented localization. -/
theorem principal_transition_projection {P : Type*} [CommRing P] [Algebra R P]
    (I : Ideal P) (r : P) {s t : Finset I} (hst : s ≤ t) (x : Localization.Away r) :
    FiniteRelationLocalization.transition R I r hst
        (PrincipalQuotientProjection.projection (FiniteRelationModel.relations I s) r x) =
      PrincipalQuotientProjection.projection (FiniteRelationModel.relations I t) r x := by
  have h : (FiniteRelationLocalization.transition R I r hst).toRingHom.comp
      (PrincipalQuotientProjection.projection (FiniteRelationModel.relations I s) r) =
      PrincipalQuotientProjection.projection (FiniteRelationModel.relations I t) r := by
    apply IsLocalization.ringHom_ext (Submonoid.powers r)
    ext p
    change FiniteRelationLocalization.transition R I r hst
      (PrincipalQuotientProjection.projection (FiniteRelationModel.relations I s) r
        (algebraMap P (Localization.Away r) p)) =
      PrincipalQuotientProjection.projection (FiniteRelationModel.relations I t) r
        (algebraMap P (Localization.Away r) p)
    rw [PrincipalQuotientProjection.projection_algebraMap,
      PrincipalQuotientProjection.projection_algebraMap,
      FiniteRelationLocalization.transition_algebraMap]
    rfl
  exact RingHom.congr_fun h x

variable {ι : Type v} [Finite ι]
  (n : ι → ℕ) (r : ∀ i, MvPolynomial (Fin (n i)) R)
  (I : ∀ i, Ideal (MvPolynomial (Fin (n i)) R))
  {E : ι → ι → Type w} [∀ i j, Finite (E i j)]

/-- Cofinal principal refinements preserve every old arrow square and original recovery. -/
theorem exists_principal_diagram_refinement
    (F : ∀ i j, E i j →
      FiniteRelationLocalization.Quotient (I i) (r i) →ₐ[R]
        FiniteRelationLocalization.Quotient (I j) (r j))
    (s b : ∀ i, Finset (I i))
    (G : ∀ i j, E i j →
      FiniteRelationLocalization.Stage (I i) (r i) (s i) →ₐ[R]
        FiniteRelationLocalization.Stage (I j) (r j) (s j))
    (hG : ∀ i j e, (FiniteRelationLocalization.toQuotient R (I j) (r j) (s j)).comp
      (G i j e) =
      (F i j e).comp (FiniteRelationLocalization.toQuotient R (I i) (r i) (s i))) :
    ∃ (t : ∀ i, Finset (I i)) (hst : s ≤ t), b ≤ t ∧
      ∃ H : ∀ i j, E i j →
        FiniteRelationLocalization.Stage (I i) (r i) (t i) →ₐ[R]
          FiniteRelationLocalization.Stage (I j) (r j) (t j),
        (∀ i j e, (H i j e).comp
            (FiniteRelationLocalization.transition R (I i) (r i) (hst i)) =
          (FiniteRelationLocalization.transition R (I j) (r j) (hst j)).comp (G i j e)) ∧
        ∀ i j e, (FiniteRelationLocalization.toQuotient R (I j) (r j) (t j)).comp
            (H i j e) =
          (F i j e).comp (FiniteRelationLocalization.toQuotient R (I i) (r i) (t i)) := by
  classical
  choose f hfac hf v hv using fun i j e ↦
    PrincipalQuotientProjection.exists_representatives (n i)
      (FiniteRelationModel.relations (I i) (s i)) (r i)
      (FiniteRelationModel.relations (I j) (s j)) (r j) (G i j e)
  have hfull (i j) (e : E i j) (p) :
      PrincipalQuotientProjection.projection (I j) (r j) (f i j e p) =
        F i j e (algebraMap _ _ (Ideal.Quotient.mk (I i) p)) := by
    rw [← FiniteRelationLocalization.toQuotient_projection R (I j) (r j) (s j), hfac]
    have h := AlgHom.congr_fun (hG i j e)
      (algebraMap _ _ (Ideal.Quotient.mk (FiniteRelationModel.relations (I i) (s i)) p))
    simpa only [AlgHom.comp_apply, FiniteRelationLocalization.toQuotient_algebraMap,
      FiniteRelationModel.toQuotient_mk] using h
  have hfI (i j) (e : E i j) : I i ≤
      ((I j).map (algebraMap _ (Localization.Away (r j)))).comap (f i j e).toRingHom := by
    intro p hp
    change f i j e p ∈ (I j).map (algebraMap _ (Localization.Away (r j)))
    rw [← PrincipalQuotientProjection.ker_projection, RingHom.mem_ker, hfull]
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero, map_zero]
  have hvI (i j) (e : E i j) : f i j e (r i) * v i j e - 1 ∈
      (I j).map (algebraMap _ (Localization.Away (r j))) :=
    Ideal.map_mono (FiniteRelationModel.relations_le (I j) (s j)) (hv i j e)
  obtain ⟨t, ht, H, hH⟩ := exists_principal_stages_of_representatives n r I
    f hfI v hvI (fun i ↦ s i ∪ b i)
  have hst : s ≤ t := fun i ↦ Finset.subset_union_left.trans (ht i)
  refine ⟨t, hst, fun i ↦ Finset.subset_union_right.trans (ht i), H, ?_, ?_⟩
  · intro i j e
    apply AlgHom.coe_ringHom_injective
    apply PrincipalQuotientProjection.hom_ext
      (FiniteRelationModel.relations (I i) (s i)) (r i)
    intro p
    change H i j e (FiniteRelationLocalization.transition R (I i) (r i) (hst i)
      (algebraMap _ _ (Ideal.Quotient.mk (FiniteRelationModel.relations (I i) (s i)) p))) =
      FiniteRelationLocalization.transition R (I j) (r j) (hst j)
        (G i j e (algebraMap _ _
          (Ideal.Quotient.mk (FiniteRelationModel.relations (I i) (s i)) p)))
    rw [FiniteRelationLocalization.transition_algebraMap, FiniteRelationModel.transition_mk,
      hH, ← hfac, principal_transition_projection]
  · intro i j e
    apply AlgHom.coe_ringHom_injective
    apply PrincipalQuotientProjection.hom_ext
      (FiniteRelationModel.relations (I i) (t i)) (r i)
    intro p
    change FiniteRelationLocalization.toQuotient R (I j) (r j) (t j)
      (H i j e (algebraMap _ _
        (Ideal.Quotient.mk (FiniteRelationModel.relations (I i) (t i)) p))) =
      F i j e (FiniteRelationLocalization.toQuotient R (I i) (r i) (t i)
        (algebraMap _ _ (Ideal.Quotient.mk (FiniteRelationModel.relations (I i) (t i)) p)))
    rw [hH, FiniteRelationLocalization.toQuotient_projection,
      FiniteRelationLocalization.toQuotient_algebraMap]
    exact hfull i j e p

end FLT.Mazur.FinitePolynomialCoefficients
