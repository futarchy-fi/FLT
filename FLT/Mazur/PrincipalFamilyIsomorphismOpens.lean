/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalFamilyIsomorphismLimits

/-!
# Genuine open immersions from finite overlap models

The common overlap embeds as the chosen principal open of every source chart.
These are actual open immersions, with the intended basic-open images, and
the coordinate identifications recover the original scheme isomorphisms.
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

/-- A genuine isomorphism between the two finite principal-open spectra. -/
def principalIsoFamilyStageIso (x : PrincipalFamilyIsomorphismStage a b e) (i : ι) :
    Spec (.of (PrincipalStage R B b x.val.target)) ≅
      Spec (.of (PrincipalStage R (A i) (a i) (x.val.source i))) :=
  Scheme.Spec.mapIso ((principalFamilyStageEquiv a b e x i).toRingEquiv.toCommRingCatIso.op)

/-- The common finite overlap is an open subscheme of each ambient source chart. -/
def principalIsoFamilyOpen (x : PrincipalFamilyIsomorphismStage a b e) (i : ι) :
    Spec (.of (PrincipalStage R B b x.val.target)) ⟶
      Spec (.of (Stage R (A i) (x.val.source i))) :=
  (principalIsoFamilyStageIso a b e x i).hom ≫
    PrincipalLocalizationSquare.inclusion
      (Ideal.Quotient.mk (FiniteRelationModel.relations (relationIdeal R (A i))
        (x.val.source i)) (principalRepresentative R (A i) (a i)))

/-- Coordinate isomorphisms followed by principal inclusions are open immersions. -/
instance principalIsoFamilyOpen_isOpenImmersion (x : PrincipalFamilyIsomorphismStage a b e)
    (i : ι) : IsOpenImmersion (principalIsoFamilyOpen a b e x i) := by
  dsimp only [principalIsoFamilyOpen]
  infer_instance

omit [Finite ι] in
/-- The overlap image is exactly the requested finite-stage basic open. -/
theorem principalIsoFamilyOpen_opensRange (x : PrincipalFamilyIsomorphismStage a b e) (i : ι) :
    (principalIsoFamilyOpen a b e x i).opensRange =
      PrimeSpectrum.basicOpen (Ideal.Quotient.mk
        (FiniteRelationModel.relations (relationIdeal R (A i)) (x.val.source i))
          (principalRepresentative R (A i) (a i))) := by
  dsimp only [principalIsoFamilyOpen]
  rw [Scheme.Hom.opensRange_comp_of_isIso,
    PrincipalLocalizationSquare.inclusion_opensRange]

omit [Finite ι] in
/-- Every finite isomorphism commutes with the projections from the original principal opens. -/
theorem principalIsoFamilySchemeIso_fac (x : PrincipalFamilyIsomorphismStage a b e) (i : ι) :
    Spec.map (CommRingCat.ofHom (e i).toAlgHom.toRingHom) ≫
        (principalIsoFamilySourceCone a b e i).π.app (.op x) =
      (principalIsoFamilyTargetCone a b e).π.app (.op x) ≫
        (principalIsoFamilyStageIso a b e x i).hom := by
  exact principalFamilySchemeMap_fac a b (fun i ↦ (e i).toAlgHom) i x.val

omit [Finite ι] in
/-- The actual overlap-to-chart maps recover the original principal-open inclusions. -/
theorem principalIsoFamilyOpen_fac (x : PrincipalFamilyIsomorphismStage a b e) (i : ι) :
    (principalIsoFamilyTargetCone a b e).π.app (.op x) ≫
        principalIsoFamilyOpen a b e x i =
      Spec.map (CommRingCat.ofHom (e i).toAlgHom.toRingHom) ≫
        PrincipalLocalizationSquare.inclusion (a i) ≫
          (affineCone R (A i)).π.app (.op (x.val.source i)) := by
  let j : Spec (.of (PrincipalStage R (A i) (a i) (x.val.source i))) ⟶
      Spec (.of (Stage R (A i) (x.val.source i))) :=
    PrincipalLocalizationSquare.inclusion
      (Ideal.Quotient.mk (FiniteRelationModel.relations (relationIdeal R (A i))
        (x.val.source i)) (principalRepresentative R (A i) (a i)))
  let f : Spec (.of (Localization.Away b)) ⟶ Spec (.of (Localization.Away (a i))) :=
    Spec.map (CommRingCat.ofHom (e i).toAlgHom.toRingHom)
  let p : Spec (.of (Localization.Away b)) ⟶ Spec (.of (PrincipalStage R B b x.val.target)) :=
    (principalIsoFamilyTargetCone a b e).π.app (.op x)
  let q : Spec (.of (Localization.Away (a i))) ⟶
      Spec (.of (PrincipalStage R (A i) (a i) (x.val.source i))) :=
    (principalIsoFamilySourceCone a b e i).π.app (.op x)
  let d : Spec (.of (PrincipalStage R B b x.val.target)) ⟶
      Spec (.of (PrincipalStage R (A i) (a i) (x.val.source i))) :=
    (principalIsoFamilyStageIso a b e x i).hom
  have hf : f ≫ q = p ≫ d := principalIsoFamilySchemeIso_fac a b e x i
  have hq : q ≫ j = PrincipalLocalizationSquare.inclusion (a i) ≫
      (affineCone R (A i)).π.app (.op (x.val.source i)) :=
    (principalProjection_isPullback R (A i) (a i) (x.val.source i)).w
  change p ≫ d ≫ j = f ≫ _
  rw [← Category.assoc, ← hf, Category.assoc, hq]

end FLT.Mazur.FiniteTypeRelationModel
