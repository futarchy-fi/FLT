/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalFamilyIsomorphismStages
public import FLT.Mazur.PrincipalFamilyLimits

/-!
# Recovering overlap rings and schemes through actual isomorphisms

All original principal opens are limits of their finite models on the cofinal
isomorphism subsystem. Their coordinate identifications form natural
isomorphisms of rings and of affine inverse systems.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v

variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : Type u} [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
  (a : ∀ i, A i) (b : B) (e : ∀ i, Localization.Away (a i) ≃ₐ[R] Localization.Away b)

/-- Source rings on the cofinal isomorphism index. -/
def principalIsoFamilySourceDiagram (i : ι) :
    PrincipalFamilyIsomorphismStage a b e ⥤ CommRingCat.{u} :=
  principalFamilyIsomorphismIndex a b e ⋙
    principalFamilySourceDiagram a b (fun i ↦ (e i).toAlgHom) i

/-- Common target rings on the same index. -/
def principalIsoFamilyTargetDiagram :
    PrincipalFamilyIsomorphismStage a b e ⥤ CommRingCat.{u} :=
  principalFamilyIsomorphismIndex a b e ⋙
    principalFamilyTargetDiagram a b (fun i ↦ (e i).toAlgHom)

/-- Source projections to the original principal ring. -/
def principalIsoFamilySourceCocone (i : ι) : Cocone (principalIsoFamilySourceDiagram a b e i) :=
  (principalFamilySourceCocone a b (fun i ↦ (e i).toAlgHom) i).whisker
    (principalFamilyIsomorphismIndex a b e)

/-- Target projections to the original common overlap ring. -/
def principalIsoFamilyTargetCocone : Cocone (principalIsoFamilyTargetDiagram a b e) :=
  (principalFamilyTargetCocone a b (fun i ↦ (e i).toAlgHom)).whisker
    (principalFamilyIsomorphismIndex a b e)

/-- Source colimits are unchanged by imposing actual invertibility. -/
def principalIsoFamilySourceIsColimit (i : ι) :
    IsColimit (principalIsoFamilySourceCocone a b e i) :=
  (Functor.Final.isColimitWhiskerEquiv (principalFamilyIsomorphismIndex a b e)
    (principalFamilySourceCocone a b (fun i ↦ (e i).toAlgHom) i)).symm
      (principalFamilySourceIsColimit a b (fun i ↦ (e i).toAlgHom) i)

/-- The target colimit is unchanged by imposing actual invertibility. -/
def principalIsoFamilyTargetIsColimit : IsColimit (principalIsoFamilyTargetCocone a b e) :=
  (Functor.Final.isColimitWhiskerEquiv (principalFamilyIsomorphismIndex a b e)
    (principalFamilyTargetCocone a b (fun i ↦ (e i).toAlgHom))).symm
      (principalFamilyTargetIsColimit a b (fun i ↦ (e i).toAlgHom))

/-- Actual coordinate isomorphisms commute with all refinements. -/
def principalIsoFamilyRingIso (i : ι) :
    principalIsoFamilySourceDiagram a b e i ≅ principalIsoFamilyTargetDiagram a b e :=
  NatIso.ofComponents (fun x ↦
    (principalFamilyStageEquiv a b e x i).toRingEquiv.toCommRingCatIso) (by
      intro x y h
      apply CommRingCat.hom_ext
      exact congrArg AlgHom.toRingHom ((leOfHom h).choose_spec.choose_spec i))

/-- Original source schemes receive the inverse-limit projections. -/
def principalIsoFamilySourceCone (i : ι) :
    Cone ((principalIsoFamilySourceDiagram a b e i).op ⋙ Scheme.Spec) :=
  Scheme.Spec.mapCone (principalIsoFamilySourceCocone a b e i).op

/-- The original common target receives its inverse-limit projections. -/
def principalIsoFamilyTargetCone :
    Cone ((principalIsoFamilyTargetDiagram a b e).op ⋙ Scheme.Spec) :=
  Scheme.Spec.mapCone (principalIsoFamilyTargetCocone a b e).op

/-- The original source is the inverse limit of these isomorphic finite models. -/
def principalIsoFamilySourceIsLimit (i : ι) : IsLimit (principalIsoFamilySourceCone a b e i) :=
  isLimitOfPreserves Scheme.Spec (principalIsoFamilySourceIsColimit a b e i).op

/-- The original overlap target is the inverse limit on the same index. -/
def principalIsoFamilyTargetIsLimit : IsLimit (principalIsoFamilyTargetCone a b e) :=
  isLimitOfPreserves Scheme.Spec (principalIsoFamilyTargetIsColimit a b e).op

/-- Coordinate identifications are natural isomorphisms of affine inverse systems. -/
def principalIsoFamilySchemeIso (i : ι) :
    (principalIsoFamilyTargetDiagram a b e).op ⋙ Scheme.Spec ≅
      (principalIsoFamilySourceDiagram a b e i).op ⋙ Scheme.Spec :=
  Functor.isoWhiskerRight (NatIso.op (principalIsoFamilyRingIso a b e i)) Scheme.Spec

omit [Finite ι] in
/-- The finite coordinate isomorphisms recover the original ring isomorphisms. -/
theorem principalIsoFamilyRingIso_fac (i : ι) (x : PrincipalFamilyIsomorphismStage a b e) :
    (principalIsoFamilyRingIso a b e i).hom.app x ≫
        (principalIsoFamilyTargetCocone a b e).ι.app x =
      (principalIsoFamilySourceCocone a b e i).ι.app x ≫
        CommRingCat.ofHom (e i).toAlgHom.toRingHom := by
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (x.val.fac i)

end FLT.Mazur.FiniteTypeRelationModel
