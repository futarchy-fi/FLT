/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicBaseChangeAddition
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
/-! # The canonical group object under coefficient extension

The geometric base-change isomorphism respects the canonical pullback
group structure. The proof compares the unit and multiplication after
the two pullback projections, using compatibility of global addition.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable (S : Type u) [CommRing S] [Algebra R S]

/-- The underlying curve pulled back to the coefficient extension. -/
abbrev coefficientPullbackGroup : Over (Spec (.of S)) :=
  Over.mk (pullback.snd (toBase W) (Spec.map (CommRingCat.ofHom (algebraMap R S))))

/-- The canonical group structure obtained by pullback. -/
instance coefficientPullbackGrpObj [IsNoetherianRing R] [_root_.IsReduced R] [W.IsElliptic] :
    GrpObj (coefficientPullbackGroup W S) :=
  Over.grpObjMkPullbackSnd

/-- The pullback group is commutative. -/
instance coefficientPullbackCommGrpObj [IsNoetherianRing R] [_root_.IsReduced R]
    [W.IsElliptic] : CommGrpObj (coefficientPullbackGroup W S) where
  mul_comm := by
    exact (Over.isCommMonObj_mk_pullbackSnd (f := toBase W)
      (g := Spec.map (CommRingCat.ofHom (algebraMap R S)))).mul_comm

/-- The geometric coefficient-extension isomorphism over the new base. -/
def coefficientGroupIso :
    groupModel (W.map (algebraMap R S)) ≅ coefficientPullbackGroup W S :=
  Over.isoMk (baseChangeIso W S) (baseChangeIso_hom_snd W S)

/-- Maps to the pullback are determined by their curve projection. -/
theorem coefficientPullbackHom_ext {X : Over (Spec (.of S))}
    (f g : X ⟶ coefficientPullbackGroup W S)
    (h : f.left ≫ pullback.fst _ _ = g.left ≫ pullback.fst _ _) : f = g := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact h
  · exact f.w.trans g.w.symm

/-- The pullback unit projects to the original point at infinity. -/
theorem coefficientPullback_one_fst [IsNoetherianRing R] [_root_.IsReduced R] [W.IsElliptic] :
    (η[coefficientPullbackGroup W S]).left ≫
        pullback.fst (toBase W) (Spec.map (CommRingCat.ofHom (algebraMap R S))) =
      Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ infinity W := by
  rw [Over.grpObjMkPullbackSnd_one, Over.comp_left, Category.assoc]
  change (Functor.LaxMonoidal.ε
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S))))).left ≫
      pullback.lift
        (pullback.fst (𝟙 (Spec (.of R)))
          (Spec.map (CommRingCat.ofHom (algebraMap R S))) ≫ infinity W)
        (pullback.snd (𝟙 (Spec (.of R)))
          (Spec.map (CommRingCat.ofHom (algebraMap R S))))
        _ ≫ pullback.fst _ _ = _
  rw [pullback.lift_fst, Over.ε_pullback_left]
  have h : pullback.fst (𝟙 (Spec (.of R)))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) =
      pullback.snd (𝟙 (Spec (.of R)))
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
    simpa using (pullback.condition (f := 𝟙 (Spec (.of R)))
      (g := Spec.map (CommRingCat.ofHom (algebraMap R S))))
  rw [h]
  simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

/-- Coefficient extension preserves the group unit. -/
theorem coefficientGroupIso_one [IsNoetherianRing R] [_root_.IsReduced R]
    [IsNoetherianRing S] [_root_.IsReduced S] [W.IsElliptic] :
    η[groupModel (W.map (algebraMap R S))] ≫ (coefficientGroupIso W S).hom =
      η[coefficientPullbackGroup W S] := by
  apply coefficientPullbackHom_ext W S
  rw [Over.comp_left, coefficientPullback_one_fst, Category.assoc]
  change infinity (W.map (algebraMap R S)) ≫ (baseChangeIso W S).hom ≫
    pullback.fst _ _ = _
  rw [baseChangeIso_hom_fst, infinity_coefficientMorphism]

/-- The pair of curve projections from the product over the new base. -/
def coefficientPullbackPair :
    (coefficientPullbackGroup W S ⊗ coefficientPullbackGroup W S).left ⟶
      (groupModel W ⊗ groupModel W).left :=
  pullback.lift
    (pullback.fst (coefficientPullbackGroup W S).hom (coefficientPullbackGroup W S).hom ≫
      pullback.fst (toBase W) (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (pullback.snd (coefficientPullbackGroup W S).hom (coefficientPullbackGroup W S).hom ≫
      pullback.fst (toBase W) (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (by
      change (_ ≫ pullback.fst (toBase W)
          (Spec.map (CommRingCat.ofHom (algebraMap R S)))) ≫ toBase W =
        (_ ≫ pullback.fst (toBase W)
          (Spec.map (CommRingCat.ofHom (algebraMap R S)))) ≫ toBase W
      simp only [Category.assoc, pullback.condition]
      simpa only [Category.assoc, coefficientPullbackGroup, Over.mk_hom] using
        congrArg (fun f => f ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))
          (pullback.condition (f := (coefficientPullbackGroup W S).hom)
            (g := (coefficientPullbackGroup W S).hom)))

/-- Pullback multiplication projects to the original addition. -/
theorem coefficientPullback_mul_fst [IsNoetherianRing R] [_root_.IsReduced R] [W.IsElliptic] :
    (μ[coefficientPullbackGroup W S]).left ≫
        pullback.fst (toBase W) (Spec.map (CommRingCat.ofHom (algebraMap R S))) =
      coefficientPullbackPair W S ≫ addition W := by
  rw [Over.grpObjMkPullbackSnd_mul, Over.comp_left, Category.assoc]
  change (Functor.LaxMonoidal.μ
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S))))
        (groupModel W) (groupModel W)).left ≫
      pullback.lift
        (pullback.fst (groupModel W ⊗ groupModel W).hom
          (Spec.map (CommRingCat.ofHom (algebraMap R S))) ≫ addition W)
        (pullback.snd (groupModel W ⊗ groupModel W).hom
          (Spec.map (CommRingCat.ofHom (algebraMap R S))))
        _ ≫ pullback.fst _ _ = _
  rw [pullback.lift_fst, ← Category.assoc]
  apply congrArg (fun f => f ≫ addition W)
  apply pullback.hom_ext
  · simp only [coefficientPullbackPair, pullback.lift_fst, Category.assoc]
    exact Over.μ_pullback_left_fst_fst
      (f := Spec.map (CommRingCat.ofHom (algebraMap R S))) (groupModel W) (groupModel W)
  · simp only [coefficientPullbackPair, pullback.lift_snd, Category.assoc]
    exact Over.μ_pullback_left_fst_snd
      (f := Spec.map (CommRingCat.ofHom (algebraMap R S))) (groupModel W) (groupModel W)

/-- The underlying map is the geometric base-change isomorphism. -/
@[simp] theorem coefficientGroupIso_hom_left :
    (coefficientGroupIso W S).hom.left = (baseChangeIso W S).hom := rfl

/-- The base-change isomorphism preserves multiplication and the unit. -/
instance coefficientGroupIsoIsMonHom [IsNoetherianRing R] [_root_.IsReduced R]
    [IsNoetherianRing S] [_root_.IsReduced S] [W.IsElliptic] :
    IsMonHom (coefficientGroupIso W S).hom where
  one_hom := coefficientGroupIso_one W S
  mul_hom := by
    apply coefficientPullbackHom_ext W S
    simp only [Over.comp_left, Category.assoc, coefficientPullback_mul_fst,
      coefficientGroupIso_hom_left, baseChangeIso_hom_fst]
    change addition (W.map (algebraMap R S)) ≫ coefficientMorphism W S = _
    rw [addition_coefficient W S]
    dsimp only [addMorphisms]
    rw [← Category.assoc]
    apply congrArg (fun f => f ≫ addition W)
    symm
    apply pullback.hom_ext
    · simp only [coefficientPullbackPair, groupModel, coefficientPullbackGroup,
        Over.mk_hom, pullback.lift_fst, Category.assoc, Over.tensorHom_left_fst_assoc,
        coefficientGroupIso_hom_left, baseChangeIso_hom_fst]
    · simp only [coefficientPullbackPair, groupModel, coefficientPullbackGroup,
        Over.mk_hom, pullback.lift_snd, Category.assoc, Over.tensorHom_left_snd_assoc,
        coefficientGroupIso_hom_left, baseChangeIso_hom_fst]

/-- The inverse base-change isomorphism is also a group morphism. -/
instance coefficientGroupIsoInvIsMonHom [IsNoetherianRing R] [_root_.IsReduced R]
    [IsNoetherianRing S] [_root_.IsReduced S] [W.IsElliptic] :
    IsMonHom (coefficientGroupIso W S).inv := inferInstance

end WeierstrassCurve.CubicCharts
