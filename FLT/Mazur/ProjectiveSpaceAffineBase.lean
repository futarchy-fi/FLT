/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveSpaceUniverseReindex
public import FLT.Mazur.ProjectiveLinearOver

/-!
# Projective coefficient charts over the actual affine base

Transport the coefficient-spectrum projection through the canonical affine
isomorphism. The resulting projective schemes commute with affine base change;
open immersions of bases give open immersions of projective charts.

These are projective quotients of the free module of homogeneous generators.
Parametrizing lines in a section module requires its dual as that generator
module. No identification with section lines is asserted here.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.ProjectiveSpace

/-- Project the coefficient model to the actual affine scheme. -/
def affineProjection (S : Scheme.{u}) [IsAffine S] (ι : Type u) :
    space Γ(S, ⊤) ι ⟶ S :=
  baseProjection Γ(S, ⊤) ι ≫ S.isoSpec.inv

/-- Linear changes of homogeneous coordinates lie over the actual affine base. -/
@[reassoc]
lemma linearIso_affineProjection (S : Scheme.{u}) [IsAffine S] {ι κ : Type u}
    (e : (ι →₀ Γ(S, ⊤)) ≃ₗ[Γ(S, ⊤)] (κ →₀ Γ(S, ⊤))) :
    (linearIso e).hom ≫ affineProjection S κ = affineProjection S ι := by
  simp only [affineProjection, linearIso_baseProjection_assoc]

/-- The coefficient morphism lies over the original morphism of affine schemes. -/
@[reassoc]
lemma coefficientMap_affineProjection {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (ι : Type u) :
    coefficientMap f.appTop.hom ι ≫ affineProjection Y ι = affineProjection X ι ≫ f := by
  dsimp only [affineProjection]
  rw [coefficientMap_baseProjection_assoc]
  change baseProjection Γ(X, ⊤) ι ≫ Spec.map f.appTop ≫ Y.isoSpec.inv = _
  rw [Scheme.isoSpec_inv_naturality, Category.assoc]

/-- Finite projective coefficient models form the actual affine-base fiber square. -/
theorem affine_isPullback {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (ι : Type u) [Finite ι] :
    IsPullback (coefficientMap f.appTop.hom ι) (affineProjection X ι)
      (affineProjection Y ι) f := by
  apply (coefficient_isPullback_finite_universe f.appTop.hom ι).of_iso
    (Iso.refl _) (Iso.refl _) X.isoSpec.symm Y.isoSpec.symm
  · simp
  · simp [affineProjection]
  · simp [affineProjection]
  · exact Scheme.isoSpec_inv_naturality f

/-- Restricting the affine base gives an open immersion of projective charts. -/
instance affineCoefficientMap_isOpenImmersion {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) [IsOpenImmersion f] (ι : Type u) [Finite ι] :
    IsOpenImmersion (coefficientMap f.appTop.hom ι) :=
  IsOpenImmersion.of_isPullback (affine_isPullback f ι).flip inferInstance

/-- The coefficient model identifies with the actual base-changed projective scheme. -/
def affinePullbackIso {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (ι : Type u) [Finite ι] :
    space Γ(X, ⊤) ι ≅ pullback (affineProjection Y ι) f :=
  (affine_isPullback f ι).isoPullback

/-- The comparison's first projection is the coefficient-change map. -/
@[reassoc (attr := simp)]
lemma affinePullbackIso_hom_fst {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (ι : Type u) [Finite ι] :
    (affinePullbackIso f ι).hom ≫ pullback.fst _ _ = coefficientMap f.appTop.hom ι :=
  (affine_isPullback f ι).isoPullback_hom_fst

/-- The comparison's second projection is the actual affine-base projection. -/
@[reassoc (attr := simp)]
lemma affinePullbackIso_hom_snd {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (ι : Type u) [Finite ι] :
    (affinePullbackIso f ι).hom ≫ pullback.snd _ _ = affineProjection X ι :=
  (affine_isPullback f ι).isoPullback_hom_snd

end FLT.Mazur.ProjectiveSpace
