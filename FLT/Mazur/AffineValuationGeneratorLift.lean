/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGeneratorRingLift
public import FLT.Mazur.SchemeSpecializationValuation
public import FLT.Mazur.SchemeScalarPrincipalNeighborhood

/-!
# Finite generator tests for extending affine valuative squares

The coordinates of the generic map and of the center keep the original
scalar square. If the finite generators lie in the valuation ring, their
ring lift constructs an actual scheme lift, including both triangle identities.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AffineValuationGeneratorLift
open SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {X : Scheme} [IsAffine X]
  (s : R →+* Γ(X, ⊤))

/-- Coordinates of the actual generic map, with values in the fraction field. -/
def genericCoordinates (S : ValuativeCommSq (scalarMorphism s)) : Γ(X, ⊤) →+* S.K :=
  (Spec.preimage (S.i₁ ≫ X.toSpecΓ)).hom

/-- Coordinates of the original scalar center, with values in the valuation ring. -/
def centerCoordinates (S : ValuativeCommSq (scalarMorphism s)) : R →+* S.R :=
  (Spec.preimage S.i₂).hom

omit [IsAffine X] in
/-- The valuation center contracts to precisely the original scalar prime. -/
theorem center_comap_maximalIdeal (S : ValuativeCommSq (scalarMorphism s)) :
    (IsLocalRing.maximalIdeal S.R).comap (centerCoordinates s S) =
      (S.i₂ (IsLocalRing.closedPoint S.R)).asIdeal := by
  change (Spec.map (Spec.preimage S.i₂) (IsLocalRing.closedPoint S.R)).asIdeal = _
  rw [Spec.map_preimage]

omit [IsAffine X] in
/-- The coordinate maps retain the entire original scalar square. -/
theorem coordinates_comm (S : ValuativeCommSq (scalarMorphism s)) :
    (genericCoordinates s S).comp s = (algebraMap S.R S.K).comp (centerCoordinates s S) := by
  have h := congrArg Spec.preimage S.commSq.w
  simp only [scalarMorphism, ← Category.assoc, Spec.preimage_comp, Spec.preimage_map] at h
  exact congrArg CommRingCat.Hom.hom h

/-- A lift of the actual coordinate maps gives an extension of the original scheme square. -/
theorem hasLift_of_coordinates (S : ValuativeCommSq (scalarMorphism s))
    (l : Γ(X, ⊤) →+* S.R)
    (hl : (algebraMap S.R S.K).comp l = genericCoordinates s S)
    (hs : l.comp s = centerCoordinates s S) : S.commSq.HasLift := by
  apply (CommSq.HasLift.iff S.commSq).mpr
  refine ⟨⟨Spec.map (CommRingCat.ofHom l) ≫ inv X.toSpecΓ, ?_, ?_⟩⟩
  · apply (cancel_mono X.toSpecΓ).mp
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom ((algebraMap S.R S.K).comp l)) = _
    rw [hl]
    exact Spec.map_preimage _
  · change (Spec.map (CommRingCat.ofHom l) ≫ inv X.toSpecΓ) ≫
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom s) = S.i₂
    rw [Category.assoc, IsIso.inv_hom_id_assoc, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom (l.comp s)) = _
    rw [hs]
    exact Spec.map_preimage _

omit [IsAffine X] in
/-- Any scheme lift supplies the coordinate factorization through the valuation ring. -/
theorem coordinates_of_lift (S : ValuativeCommSq (scalarMorphism s))
    (l : S.commSq.LiftStruct) :
    genericCoordinates s S = (algebraMap S.R S.K).comp
      (Spec.preimage (l.l ≫ X.toSpecΓ)).hom := by
  have h := congrArg
    (fun t : Spec (.of S.K) ⟶ X ↦ Spec.preimage (t ≫ X.toSpecΓ)) l.fac_left
  simp only [Category.assoc, Spec.preimage_comp, Spec.preimage_map] at h
  exact (congrArg CommRingCat.Hom.hom h).symm

variable (a : Finset Γ(X, ⊤))
  (ha : Subring.closure (Set.range s ∪ (a : Set Γ(X, ⊤))) = ⊤)

include ha in
/-- Regular values on finitely many generators construct an extension of the full chart map. -/
theorem hasLift_of_generators (S : ValuativeCommSq (scalarMorphism s))
    (hg : ∀ b ∈ a, genericCoordinates s S b ∈ (algebraMap S.R S.K).range) :
    S.commSq.HasLift := by
  obtain ⟨l, hl, hs⟩ := FiniteGeneratorRingLift.exists_lift s a ha
    (algebraMap S.R S.K) (IsFractionRing.injective S.R S.K)
    (genericCoordinates s S) (centerCoordinates s S) (coordinates_comm s S) hg
  exact hasLift_of_coordinates s S l hl hs

include ha in
/-- Extension is equivalent to regularity of exactly the chosen finite generator values. -/
theorem hasLift_iff_generators (S : ValuativeCommSq (scalarMorphism s)) :
    S.commSq.HasLift ↔
      ∀ b ∈ a, genericCoordinates s S b ∈ (algebraMap S.R S.K).range := by
  refine ⟨?_, hasLift_of_generators s a ha S⟩
  intro h b _
  obtain ⟨l⟩ := (CommSq.HasLift.iff S.commSq).mp h
  rw [coordinates_of_lift s S l]
  exact ⟨_, rfl⟩

include ha in
/-- Nonextension forces a pole among the fixed finite original-scalar generators. -/
theorem exists_generator_pole (S : ValuativeCommSq (scalarMorphism s))
    (h : ¬ S.commSq.HasLift) :
    ∃ b ∈ a, genericCoordinates s S b ∉ (algebraMap S.R S.K).range := by
  by_contra hn
  push Not at hn
  exact h (hasLift_of_generators s a ha S hn)

end FLT.Mazur.AffineValuationGeneratorLift
