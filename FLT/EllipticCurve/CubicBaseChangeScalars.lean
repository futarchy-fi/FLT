/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicBaseChangeNonzero
public import FLT.EllipticCurve.CubicNonzeroScalarTransport
/-! # Scalar actions under coefficient extension

The torsion base-change isomorphism intertwines the scalar action.
This descends to the restricted coefficient map on nonzero torsion.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable (S : Type u) [CommRing S] [Algebra R S]

/-- The pullback of a morphism commutes with the first projections. -/
theorem coefficientPullback_map_fst {X Y : Over (Spec (.of R))} (f : X ⟶ Y) :
    ((coefficientPullbackFunctor (R := R) S).map f).left ≫
        pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))) =
      pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))) ≫ f.left := by
  change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
  exact pullback.lift_fst _ _ _

variable [IsNoetherianRing R] [IsDomain R]
variable [IsNoetherianRing S] [IsDomain S] [W.IsElliptic]
variable (n : ℕ) [NeZero n]

/-- The torsion base-change isomorphism intertwines scalar multiplication. -/
theorem coefficientTorsionIso_scalar (a : (ZMod n)ˣ) :
    (torsionScalarIso (W.map (algebraMap R S)) n a).hom ≫
        (coefficientTorsionIso W S n).hom =
      (coefficientTorsionIso W S n).hom ≫
        (coefficientPullbackFunctor (R := R) S).map (torsionScalarIso W n a).hom := by
  have h := map_pow ((coefficientPullbackFunctor (R := R) S).homMonoidHom
    (M := torsionModel W n) (X := torsionModel W n)) (𝟙 _) a.val.val
  change (coefficientPullbackFunctor (R := R) S).map ((𝟙 (torsionModel W n)) ^ a.val.val) =
    ((coefficientPullbackFunctor (R := R) S).map (𝟙 (torsionModel W n))) ^ a.val.val at h
  rw [CategoryTheory.Functor.map_id] at h
  rw [torsionScalarIso_hom, torsionScalarIso_hom, h]
  rw [MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]

/-- The coefficient map on torsion commutes with scalar multiplication. -/
@[reassoc] theorem coefficientTorsionMorphism_scalar (a : (ZMod n)ˣ) :
    (torsionScalarIso (W.map (algebraMap R S)) n a).hom.left ≫
        coefficientTorsionMorphism W S n =
      coefficientTorsionMorphism W S n ≫ (torsionScalarIso W n a).hom.left := by
  have h := congrArg Over.Hom.left (coefficientTorsionIso_scalar W S n a)
  change _ ≫ _ = _ ≫ _ at h
  dsimp only [coefficientTorsionMorphism]
  rw [← Category.assoc, h, Category.assoc, coefficientPullback_map_fst, Category.assoc]

/-- The restricted coefficient map intertwines the scalar actions. -/
@[reassoc] theorem coefficientNonzeroTorsionMorphism_scalar (a : (ZMod n)ˣ) :
    (nonzeroTorsionScalarAction (W.map (algebraMap R S)) n a).hom.left ≫
        coefficientNonzeroTorsionMorphism W S n =
      coefficientNonzeroTorsionMorphism W S n ≫
        (nonzeroTorsionScalarAction W n a).hom.left := by
  rw [nonzeroTorsionScalarAction_hom, nonzeroTorsionScalarAction_hom]
  apply (cancel_mono (nonzeroTorsionInclusion W n).left).mp
  have h₁ := congrArg Over.Hom.left
    (nonzeroTorsionScalarHom_inclusion (W.map (algebraMap R S)) n a)
  have h₂ := congrArg Over.Hom.left (nonzeroTorsionScalarHom_inclusion W n a)
  change _ ≫ _ = _ ≫ _ at h₁ h₂
  simp only [Category.assoc, coefficientNonzeroTorsionMorphism_inclusion]
  rw [← Category.assoc, h₁, Category.assoc, coefficientTorsionMorphism_scalar,
    ← Category.assoc, ← coefficientNonzeroTorsionMorphism_inclusion, Category.assoc, h₂]

end WeierstrassCurve.CubicCharts
