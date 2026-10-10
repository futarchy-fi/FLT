/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationSpectrum
public import FLT.Mazur.FiniteTypeRelationPresentation

/-!
# Approximation of finite-type affine schemes

For every finite-type algebra over an arbitrary ring, construct a cofiltered
system of finitely presented affine schemes over the same base. Its inverse
limit is the original affine scheme, and its transitions are closed immersions.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

universe u

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
  [Algebra.FiniteType R B]

/-- The finite-relation ring system with the original algebra as cocone point. -/
def algebraCocone : Cocone (FiniteRelationModel.ringDiagram R (relationIdeal R B)) where
  pt := .of B
  ι.app s := CommRingCat.ofHom (stageMap R B s).toRingHom
  ι.naturality s t f := by
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom (stageMap_transition R B (leOfHom f))

/-- The original finite-type algebra is the colimit of the constructed stages. -/
def algebraIsColimit : IsColimit (algebraCocone R B) := by
  classical
  let _ := reflectsColimit_of_reflectsIsomorphisms
    (FiniteRelationModel.ringDiagram R (relationIdeal R B)) (forget CommRingCat)
  apply isColimitOfReflects (forget CommRingCat)
  apply Types.FilteredColimit.isColimitOf'
  · intro b
    obtain ⟨x, hx⟩ := stageMap_surjective R B ∅ b
    exact ⟨∅, x, hx.symm⟩
  · intro s x y h
    have hq : FiniteRelationModel.toQuotient R (relationIdeal R B) s x =
        FiniteRelationModel.toQuotient R (relationIdeal R B) s y :=
      (quotientEquiv R B).injective h
    obtain ⟨t, hst, ht⟩ :=
      FiniteRelationModel.exists_transition_eq R (relationIdeal R B) s x y hq
    exact ⟨t, homOfLE hst, ht⟩

/-- Finitely presented affine approximations indexed by finite sets of relations. -/
abbrev affineDiagram : (Finset (relationIdeal R B))ᵒᵖ ⥤ Scheme.{u} :=
  FiniteRelationModel.spectrumDiagram R (relationIdeal R B)

/-- The original spectrum maps compatibly to every approximation. -/
def affineCone : Cone (affineDiagram R B) :=
  Scheme.Spec.mapCone (algebraCocone R B).op

/-- The approximation recovers the original finite-type affine scheme exactly. -/
def affineIsLimit : IsLimit (affineCone R B) :=
  isLimitOfPreserves Scheme.Spec (algebraIsColimit R B).op

/-- Every approximating affine scheme is locally finitely presented over the base. -/
instance affineStage_locallyOfFinitePresentation (s : Finset (relationIdeal R B)) :
    LocallyOfFinitePresentation
      (FiniteRelationModel.stageStructure R (relationIdeal R B) s) := inferInstance

/-- The original affine scheme is a closed subscheme of each approximation. -/
instance affineProjection_isClosedImmersion (s : Finset (relationIdeal R B)) :
    IsClosedImmersion ((affineCone R B).π.app (.op s)) :=
  IsClosedImmersion.spec_of_surjective _ (stageMap_surjective R B s)

/-- The limit projections are morphisms over the original affine base. -/
theorem affineProjection_over (s : Finset (relationIdeal R B)) :
    (affineCone R B).π.app (.op s) ≫
        FiniteRelationModel.stageStructure R (relationIdeal R B) s =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  change Spec.map (CommRingCat.ofHom (stageMap R B s).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (Stage R B s))) = _
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (stageMap R B s).comp_algebraMap

end FLT.Mazur.FiniteTypeRelationModel
