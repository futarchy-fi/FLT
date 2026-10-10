/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationLocalizationColimit
public import FLT.Mazur.FiniteRelationSpectrum
public import FLT.Mazur.PrincipalLocalizationSquare

/-!
# Principal-open inverse systems with cartesian transition squares

The principal open in the original affine quotient is the inverse limit of
finitely presented principal-open models. Their inclusions into ambient
models are open immersions, and every transition and limit-projection square
is cartesian. The base ring and finite-relation index are unchanged.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.FiniteRelationLocalization

universe u

variable (R : Type u) [CommRing R] {P : Type u} [CommRing P] [Algebra R P]
  (I : Ideal P) (r : P)

/-- The principal-open models form an inverse system over the ambient index. -/
def spectrumDiagram : (Finset I)ᵒᵖ ⥤ Scheme.{u} :=
  (ringDiagram R I r).op ⋙ Scheme.Spec

/-- The original principal open maps to all its finite models. -/
def spectrumCone : Cone (spectrumDiagram R I r) :=
  Scheme.Spec.mapCone (quotientCocone R I r).op

/-- The original principal open is the inverse limit of the constructed models. -/
def spectrumIsLimit : IsLimit (spectrumCone R I r) :=
  isLimitOfPreserves Scheme.Spec (quotientIsColimit R I r).op

/-- Localized transition morphisms are closed immersions. -/
instance spectrumMap_isClosedImmersion {s t : (Finset I)ᵒᵖ} (f : s ⟶ t) :
    IsClosedImmersion ((spectrumDiagram R I r).map f) :=
  IsClosedImmersion.spec_of_surjective _ (transition_surjective R I r (leOfHom f.unop))

/-- Localized limit projections are closed immersions. -/
instance spectrumProjection_isClosedImmersion (s : Finset I) :
    IsClosedImmersion ((spectrumCone R I r).π.app (.op s)) :=
  IsClosedImmersion.spec_of_surjective _ (toQuotient_surjective R I r s)

/-- Structure morphism of the principal-open model over the original base. -/
def stageStructure (s : Finset I) : Spec (.of (Stage I r s)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Stage I r s)))

/-- Principal-open models are locally finitely presented over the original base. -/
instance stageStructure_locallyOfFinitePresentation [Algebra.FinitePresentation R P]
    (s : Finset I) : LocallyOfFinitePresentation (stageStructure R I r s) := by
  apply (LocallyOfFinitePresentation.SpecMap_iff _).mpr
  exact RingHom.finitePresentation_algebraMap.mpr inferInstance

/-- Transition squares for the open inclusions are cartesian. -/
theorem transition_isPullback {s t : Finset I} (h : s ≤ t) :
    IsPullback (Spec.map (CommRingCat.ofHom (transition R I r h).toRingHom))
      (PrincipalLocalizationSquare.inclusion
        (Ideal.Quotient.mk _ r : FiniteRelationModel.Stage I t))
      (PrincipalLocalizationSquare.inclusion
        (Ideal.Quotient.mk _ r : FiniteRelationModel.Stage I s))
      (Spec.map (CommRingCat.ofHom (FiniteRelationModel.transition R I h).toRingHom)) :=
  PrincipalLocalizationSquare.isPullback (FiniteRelationModel.transition R I h).toRingHom
    (Ideal.Quotient.mk _ r)

/-- The limiting principal open is the pullback of every principal-open model. -/
theorem projection_isPullback (s : Finset I) :
    IsPullback (Spec.map (CommRingCat.ofHom (toQuotient R I r s).toRingHom))
      (PrincipalLocalizationSquare.inclusion (Ideal.Quotient.mk I r))
      (PrincipalLocalizationSquare.inclusion
        (Ideal.Quotient.mk _ r : FiniteRelationModel.Stage I s))
      (Spec.map (CommRingCat.ofHom (FiniteRelationModel.toQuotient R I s).toRingHom)) :=
  PrincipalLocalizationSquare.isPullback (FiniteRelationModel.toQuotient R I s).toRingHom
    (Ideal.Quotient.mk _ r)

end FLT.Mazur.FiniteRelationLocalization
