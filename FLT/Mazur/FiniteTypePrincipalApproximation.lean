/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypePrincipalPresentation
public import FLT.Mazur.FiniteTypeAffineApproximation
public import FLT.Mazur.FiniteRelationLocalizationSpectrum

/-!
# Recovering original principal opens from their finite models

The cone vertex is the original localized finite-type algebra. Its spectrum
is the inverse limit of finitely presented models over the original base,
and its square with every ambient chart projection is cartesian.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

universe u

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
  [Algebra.FiniteType R B] (b : B)

/-- The original principal-open algebra is the vertex of the localized cocone. -/
def principalAlgebraCocone : Cocone
    (FiniteRelationLocalization.ringDiagram R (relationIdeal R B)
      (principalRepresentative R B b)) where
  pt := .of (Localization.Away b)
  ι.app s := CommRingCat.ofHom (principalStageMap R B b s).toRingHom
  ι.naturality s t f := by
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom (principalStageMap_transition R B b (leOfHom f))

/-- The localized stages recover the original principal-open algebra exactly. -/
def principalAlgebraIsColimit : IsColimit (principalAlgebraCocone R B b) := by
  classical
  let _ := reflectsColimit_of_reflectsIsomorphisms
    (FiniteRelationLocalization.ringDiagram R (relationIdeal R B) (principalRepresentative R B b))
    (forget CommRingCat)
  apply isColimitOfReflects (forget CommRingCat)
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    obtain ⟨y, hy⟩ := principalStageMap_surjective R B b ∅ x
    exact ⟨∅, y, hy.symm⟩
  · intro s x y h
    have he : FiniteRelationLocalization.toQuotient R (relationIdeal R B)
        (principalRepresentative R B b) s x =
      FiniteRelationLocalization.toQuotient R (relationIdeal R B)
        (principalRepresentative R B b) s y := (principalQuotientEquiv R B b).injective h
    obtain ⟨t, hst, ht⟩ := FiniteRelationLocalization.exists_transition_eq R
      (relationIdeal R B) (principalRepresentative R B b) s x y he
    exact ⟨t, homOfLE hst, ht⟩

/-- Principal-open models use the ambient chart's finite-relation index. -/
abbrev principalAffineDiagram : (Finset (relationIdeal R B))ᵒᵖ ⥤ Scheme.{u} :=
  FiniteRelationLocalization.spectrumDiagram R (relationIdeal R B) (principalRepresentative R B b)

/-- The actual principal open maps to every finite model. -/
def principalAffineCone : Cone (principalAffineDiagram R B b) :=
  Scheme.Spec.mapCone (principalAlgebraCocone R B b).op

/-- The original principal-open scheme is the limit of its finite models. -/
def principalAffineIsLimit : IsLimit (principalAffineCone R B b) :=
  isLimitOfPreserves Scheme.Spec (principalAlgebraIsColimit R B b).op

/-- Every projection to a principal-open model is a closed immersion. -/
instance principalProjection_isClosedImmersion (s : Finset (relationIdeal R B)) :
    IsClosedImmersion ((principalAffineCone R B b).π.app (.op s)) :=
  IsClosedImmersion.spec_of_surjective _ (principalStageMap_surjective R B b s)

/-- Original principal opens are the cartesian pullbacks of their finite-stage models. -/
theorem principalProjection_isPullback (s : Finset (relationIdeal R B)) :
    IsPullback ((principalAffineCone R B b).π.app (.op s))
      (PrincipalLocalizationSquare.inclusion b)
      (PrincipalLocalizationSquare.inclusion
        (Ideal.Quotient.mk (FiniteRelationModel.relations (relationIdeal R B) s)
          (principalRepresentative R B b)))
      ((affineCone R B).π.app (.op s)) := by
  change IsPullback (Spec.map (CommRingCat.ofHom (principalStageMap R B b s).toRingHom))
    (PrincipalLocalizationSquare.inclusion b)
    (PrincipalLocalizationSquare.inclusion
      (Ideal.Quotient.mk (FiniteRelationModel.relations (relationIdeal R B) s)
        (principalRepresentative R B b)))
    (Spec.map (CommRingCat.ofHom (stageMap R B s).toRingHom))
  apply IsOpenImmersion.isPullback
  · change PrincipalLocalizationSquare.inclusion b ≫
        Spec.map (CommRingCat.ofHom (stageMap R B s).toRingHom) =
      Spec.map (CommRingCat.ofHom (principalStageMap R B b s).toRingHom) ≫
        PrincipalLocalizationSquare.inclusion _
    simp only [PrincipalLocalizationSquare.inclusion, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact (principalStageMap_algebraMap R B b s x).symm
  · rw [PrincipalLocalizationSquare.inclusion_opensRange,
      PrincipalLocalizationSquare.inclusion_opensRange]
    change PrimeSpectrum.basicOpen (stageMap R B s
      (Ideal.Quotient.mk _ (principalRepresentative R B b))) = PrimeSpectrum.basicOpen b
    rw [stageMap_mk, principalRepresentative_spec]

/-- The principal-open projection preserves the structure map over the original base. -/
theorem principalProjection_over (s : Finset (relationIdeal R B)) :
    (principalAffineCone R B b).π.app (.op s) ≫
      FiniteRelationLocalization.stageStructure R (relationIdeal R B)
        (principalRepresentative R B b) s =
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away b))) := by
  change Spec.map (CommRingCat.ofHom (principalStageMap R B b s).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (PrincipalStage R B b s))) = _
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (principalStageMap R B b s).comp_algebraMap

end FLT.Mazur.FiniteTypeRelationModel
