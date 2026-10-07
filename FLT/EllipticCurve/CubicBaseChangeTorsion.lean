/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicBaseChangeGroup
public import FLT.EllipticCurve.CubicTorsionTransport
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
/-! # Base change of the represented torsion group

The actual n-torsion scheme commutes with coefficient extension.
The comparison preserves the inclusion into the curve and the group law;
it uses preservation of equalizers by the pullback functor.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable (S : Type u) [CommRing S] [Algebra R S]
variable [IsNoetherianRing R] [_root_.IsReduced R]
variable [IsNoetherianRing S] [_root_.IsReduced S] [W.IsElliptic]

/-- The pullback functor for coefficient extension. -/
abbrev coefficientPullbackFunctor :=
  Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))

/-- The canonical group structure on the pulled-back torsion scheme. -/
instance coefficientTorsionPullbackGrpObj (n : ℕ) :
    GrpObj ((coefficientPullbackFunctor (R := R) S).obj (torsionModel W n)) :=
  ((coefficientPullbackFunctor (R := R) S).mapGrp.obj (.mk (torsionModel W n))).grp

/-- The pulled-back torsion inclusion is a group morphism. -/
instance coefficientTorsionPullbackInclusionIsMonHom (n : ℕ) :
    IsMonHom ((coefficientPullbackFunctor (R := R) S).map (torsionInclusion W n)) := by
  exact CategoryTheory.Functor.map.instIsMonHom
    (F := coefficientPullbackFunctor (R := R) S) (f := torsionInclusion W n)

omit [IsNoetherianRing S] [_root_.IsReduced S] in
/-- Pullback preserves multiplication by any natural number. -/
theorem coefficientPullback_multiplication (n : ℕ) :
    (coefficientPullbackFunctor (R := R) S).map (multiplicationOver W n) =
      (𝟙 (coefficientPullbackGroup W S)) ^ n := by
  let : GrpObj ((coefficientPullbackFunctor (R := R) S).obj (groupModel W)) :=
    coefficientPullbackGrpObj W S
  have h := map_pow ((coefficientPullbackFunctor (R := R) S).homMonoidHom
    (M := groupModel W) (X := groupModel W)) (𝟙 _) n
  change (coefficientPullbackFunctor (R := R) S).map ((𝟙 (groupModel W)) ^ n) =
    ((coefficientPullbackFunctor (R := R) S).map (𝟙 (groupModel W))) ^ n at h
  rw [CategoryTheory.Functor.map_id] at h
  exact h

/-- The base-change group isomorphism intertwines multiplication by n. -/
theorem coefficientGroupIso_multiplication (n : ℕ) :
    multiplicationOver (W.map (algebraMap R S)) n ≫ (coefficientGroupIso W S).hom =
      (coefficientGroupIso W S).hom ≫
        (coefficientPullbackFunctor (R := R) S).map (multiplicationOver W n) := by
  rw [coefficientPullback_multiplication]
  simp only [multiplicationOver, MonObj.pow_comp, MonObj.comp_pow,
    Category.id_comp, Category.comp_id]

/-- The base-change group isomorphism intertwines the zero endomorphisms. -/
theorem coefficientGroupIso_zero :
    (1 : groupModel (W.map (algebraMap R S)) ⟶ groupModel (W.map (algebraMap R S))) ≫
        (coefficientGroupIso W S).hom =
      (coefficientGroupIso W S).hom ≫
        (coefficientPullbackFunctor (R := R) S).map (1 : groupModel W ⟶ groupModel W) := by
  rw [Functor.map_one]
  simp only [MonObj.one_comp, MonObj.comp_one]

/-- The actual n-torsion scheme is the base change of the original n-torsion. -/
def coefficientTorsionIso (n : ℕ) :
    torsionModel (W.map (algebraMap R S)) n ≅
      (coefficientPullbackFunctor (R := R) S).obj (torsionModel W n) :=
  (HasLimit.isoOfNatIso (parallelPairIso
    (multiplicationOver (W.map (algebraMap R S)) n) 1
    ((coefficientPullbackFunctor (R := R) S).map (multiplicationOver W n))
    ((coefficientPullbackFunctor (R := R) S).map 1)
    (coefficientGroupIso W S) (coefficientGroupIso W S)
    (coefficientGroupIso_multiplication W S n) (coefficientGroupIso_zero W S))) ≪≫
  (PreservesEqualizer.iso (coefficientPullbackFunctor (R := R) S)
    (multiplicationOver W n) 1).symm

/-- The torsion comparison agrees with the curve comparison after inclusion. -/
@[reassoc (attr := simp)] theorem coefficientTorsionIso_inclusion (n : ℕ) :
    (coefficientTorsionIso W S n).hom ≫
        (coefficientPullbackFunctor (R := R) S).map (torsionInclusion W n) =
      torsionInclusion (W.map (algebraMap R S)) n ≫ (coefficientGroupIso W S).hom := by
  simp only [coefficientTorsionIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    torsionInclusion, PreservesEqualizer.iso_inv_ι]
  exact HasLimit.isoOfNatIso_hom_π _ WalkingParallelPair.zero

/-- The torsion base-change comparison is a group morphism. -/
instance coefficientTorsionIsoIsMonHom (n : ℕ) :
    IsMonHom (coefficientTorsionIso W S n).hom where
  one_hom := by
    apply (cancel_mono ((coefficientPullbackFunctor (R := R) S).map
      (torsionInclusion W n))).mp
    simp only [Category.assoc, coefficientTorsionIso_inclusion, IsMonHom.one_hom]
  mul_hom := by
    apply (cancel_mono ((coefficientPullbackFunctor (R := R) S).map
      (torsionInclusion W n))).mp
    simp only [Category.assoc, coefficientTorsionIso_inclusion, IsMonHom.mul_hom,
      tensorHom_comp_tensorHom_assoc, coefficientTorsionIso_inclusion]

/-- Its inverse is a group morphism as well. -/
instance coefficientTorsionIsoInvIsMonHom (n : ℕ) :
    IsMonHom (coefficientTorsionIso W S n).inv := inferInstance

end WeierstrassCurve.CubicCharts
