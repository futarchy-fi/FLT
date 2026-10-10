/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationColimit
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Affine inverse limits of finite-relation models

The spectrum of an arbitrary quotient is the inverse limit of the spectra
of its finite-relation stages. All transition and projection maps are closed
immersions. The stage structure maps are finitely presented when the ambient
algebra is; this construction does not yet glue nonaffine charts.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.FiniteRelationModel

universe u

variable (R : Type u) [CommRing R] {P : Type u} [CommRing P] [Algebra R P]
  (I : Ideal P)

/-- The inverse system of finite-relation affine models. -/
def spectrumDiagram : (Finset I)ᵒᵖ ⥤ Scheme.{u} :=
  (ringDiagram R I).op ⋙ Scheme.Spec

/-- The original affine quotient maps to every finite-relation model. -/
def spectrumCone : Cone (spectrumDiagram R I) :=
  Scheme.Spec.mapCone (quotientCocone R I).op

/-- The original affine quotient is the inverse limit. -/
def spectrumIsLimit : IsLimit (spectrumCone R I) :=
  isLimitOfPreserves Scheme.Spec (quotientIsColimit R I).op

/-- Every transition of the inverse system is a closed immersion. -/
instance spectrumMap_isClosedImmersion {s t : (Finset I)ᵒᵖ} (f : s ⟶ t) :
    IsClosedImmersion ((spectrumDiagram R I).map f) :=
  IsClosedImmersion.spec_of_surjective _ (transition_surjective R I (leOfHom f.unop))

/-- In particular the inverse system has affine transition morphisms. -/
instance spectrumMap_isAffineHom {s t : (Finset I)ᵒᵖ} (f : s ⟶ t) :
    IsAffineHom ((spectrumDiagram R I).map f) := by
  dsimp [spectrumDiagram, ringDiagram]
  infer_instance

/-- Each projection from the original affine quotient is a closed immersion. -/
instance spectrumProjection_isClosedImmersion (s : Finset I) :
    IsClosedImmersion ((spectrumCone R I).π.app (.op s)) :=
  IsClosedImmersion.spec_of_surjective _ (toQuotient_surjective R I s)

/-- The structure morphism of a finite-relation affine stage. -/
def stageStructure (s : Finset I) : Spec (.of (Stage I s)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Stage I s)))

/-- Stage structure maps are locally of finite presentation. -/
instance stageStructure_locallyOfFinitePresentation [Algebra.FinitePresentation R P]
    (s : Finset I) : LocallyOfFinitePresentation (stageStructure R I s) := by
  apply (LocallyOfFinitePresentation.SpecMap_iff _).mpr
  exact RingHom.finitePresentation_algebraMap.mpr inferInstance

/-- Every transition commutes with the maps to the original affine base. -/
theorem stageStructure_transition {s t : Finset I} (h : s ≤ t) :
    Spec.map (CommRingCat.ofHom (transition R I h).toRingHom) ≫ stageStructure R I s =
      stageStructure R I t := by
  rw [stageStructure, stageStructure, ← Spec.map_comp]
  congr 1

/-- Every projection retains the original structure morphism. -/
theorem stageStructure_projection (s : Finset I) :
    (spectrumCone R I).π.app (.op s) ≫ stageStructure R I s =
      Spec.map (CommRingCat.ofHom (algebraMap R (P ⧸ I))) := by
  change Spec.map (CommRingCat.ofHom (toQuotient R I s).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (Stage I s))) = _
  rw [← Spec.map_comp]
  congr 1

end FLT.Mazur.FiniteRelationModel
