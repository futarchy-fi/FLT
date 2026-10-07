/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicVariableChangeIso
public import FLT.EllipticCurve.CubicGroupScheme
public import FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
/-! # Coordinate changes preserve the cubic group scheme

Comparison with the classical field-valued point groups proves preservation
of addition on reduced sources. Applying this to the smooth cubic product
gives a group-scheme isomorphism over every reduced noetherian base.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (C : VariableChange R)

theorem affineEvaluation_variableChange {S : Type u} [CommRing S] [Algebra R S]
    (x y : S) (h : ((C • W).map (algebraMap R S)).toAffine.Equation x y)
    (h' : (W.map (algebraMap R S)).toAffine.Equation
      ((algebraMap R S (C.u : R)) ^ 2 * x + algebraMap R S C.r)
      ((algebraMap R S (C.u : R)) ^ 3 * y +
        (algebraMap R S (C.u : R)) ^ 2 * algebraMap R S C.s * x + algebraMap R S C.t)) :
    (affineEvaluation (C • W) x y h).comp (variableChangeAffineMap W C) =
      affineEvaluation W
        ((algebraMap R S (C.u : R)) ^ 2 * x + algebraMap R S C.r)
        ((algebraMap R S (C.u : R)) ^ 3 * y +
          (algebraMap R S (C.u : R)) ^ 2 * algebraMap R S C.s * x + algebraMap R S C.t) h' := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change affineEvaluation (C • W) x y h (variableChangeAffineMap W C (coord W false i)) =
    affineEvaluation W _ _ h' (coord W false i)
  fin_cases i <;> simp [variableChangeAffineCoords]

private theorem specAlgHom_comp_of_eq {A B T : Type u}
    [CommRing A] [CommRing B] [CommRing T] [Algebra R A] [Algebra R B] [Algebra R T]
    (f : B →ₐ[R] T) (g : A →ₐ[R] B) (h : A →ₐ[R] T) (w : f.comp g = h) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ Spec.map (CommRingCat.ofHom g.toRingHom) =
      Spec.map (CommRingCat.ofHom h.toRingHom) := by
  rw [← Spec.map_comp]
  exact congrArg (fun k : A →ₐ[R] T => Spec.map (CommRingCat.ofHom k.toRingHom)) w

theorem affineFieldPoint_variableChange {S : Type u} [CommRing S] [Algebra R S]
    (x y : S) (h : ((C • W).map (algebraMap R S)).toAffine.Equation x y)
    (h' : (W.map (algebraMap R S)).toAffine.Equation
      ((algebraMap R S (C.u : R)) ^ 2 * x + algebraMap R S C.r)
      ((algebraMap R S (C.u : R)) ^ 3 * y +
        (algebraMap R S (C.u : R)) ^ 2 * algebraMap R S C.s * x + algebraMap R S C.t)) :
    (Spec.map (CommRingCat.ofHom (affineEvaluation (C • W) x y h).toRingHom) ≫
        affineChart (C • W)) ≫ variableChangeMorphism W C =
      Spec.map (CommRingCat.ofHom (affineEvaluation W _ _ h').toRingHom) ≫ affineChart W := by
  rw [Category.assoc, affineChart_variableChange, ← Category.assoc]
  exact congrArg (fun f => f ≫ affineChart W)
    (specAlgHom_comp_of_eq _ _ _ (affineEvaluation_variableChange W C x y h h'))

/-- Coordinate change on classical points after any coefficient-field extension. -/
def variableChangePointEquiv [W.IsElliptic] (K : Type u) [Field K] [Algebra R K]
    [DecidableEq K] :
    ((C • W).map (algebraMap R K)).toAffine.Point ≃+
      (W.map (algebraMap R K)).toAffine.Point :=
  (Affine.Point.equivOfEq (map_variableChange W C (algebraMap R K)).symm).trans
    (Affine.Point.equivVariableChange (W.map (algebraMap R K)) (C.map (algebraMap R K)))

theorem fieldPointMorphism_variableChange [W.IsElliptic]
    {K : Type u} [Field K] [Algebra R K] [DecidableEq K]
    (P : ((C • W).map (algebraMap R K)).toAffine.Point) :
    fieldPointMorphism (C • W) P ≫ variableChangeMorphism W C =
      fieldPointMorphism W (variableChangePointEquiv W C K P) := by
  cases P with
  | zero =>
    simp only [← Affine.Point.zero_def, map_zero, fieldPointMorphism,
      Category.assoc, infinity_variableChange]
  | some x y h =>
    unfold variableChangePointEquiv
    erw [AddEquiv.trans_apply, Affine.Point.equivOfEq_some,
      Affine.Point.equivVariableChange_some]
    exact affineFieldPoint_variableChange W C x y h.1 _

theorem addMorphisms_variableChange_field [W.IsElliptic]
    {K : Type u} [Field K] [Algebra R K]
    (f g : Spec (.of K) ⟶ scheme (C • W))
    (hf : f ≫ toBase (C • W) = Spec.map (CommRingCat.ofHom (algebraMap R K)))
    (hfg : f ≫ toBase (C • W) = g ≫ toBase (C • W)) :
    addMorphisms (C • W) f g hfg ≫ variableChangeMorphism W C =
      addMorphisms W (f ≫ variableChangeMorphism W C) (g ≫ variableChangeMorphism W C)
        (by simp only [Category.assoc, variableChange_toBase, hfg]) := by
  classical
  obtain ⟨P, rfl⟩ := fieldPointMorphism_surjective (C • W) f hf
  obtain ⟨Q, rfl⟩ := fieldPointMorphism_surjective (C • W) g (hfg.symm.trans hf)
  simp only [addMorphisms_fieldPoints, fieldPointMorphism_variableChange, map_add]

/-- The coordinate change preserves addition on every reduced scheme of points. -/
theorem addMorphisms_variableChange_of_isReduced [W.IsElliptic]
    {X : Scheme.{u}} [AlgebraicGeometry.IsReduced X]
    (f g : X ⟶ scheme (C • W)) (hfg : f ≫ toBase (C • W) = g ≫ toBase (C • W)) :
    addMorphisms (C • W) f g hfg ≫ variableChangeMorphism W C =
      addMorphisms W (f ≫ variableChangeMorphism W C) (g ≫ variableChangeMorphism W C)
        (by simp only [Category.assoc, variableChange_toBase, hfg]) := by
  apply ext_of_fromSpecResidueField_eq _ _ (toBase W) Set.univ dense_univ
  · intro x _
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.fromSpecResidueField x ≫ f ≫ toBase (C • W))
    let K : Type u := IsLocalRing.ResidueField (X.presheaf.stalk x)
    let : Algebra R K := φ.hom.toAlgebra
    have hf : (X.fromSpecResidueField x ≫ f) ≫ toBase (C • W) =
        Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
      change (X.fromSpecResidueField x ≫ f) ≫ toBase (C • W) = Spec.map φ
      simpa only [Category.assoc] using hφ.symm
    rw [← Category.assoc, addMorphisms_precomp, addMorphisms_precomp]
    simpa only [Category.assoc] using
      addMorphisms_variableChange_field W C (K := K)
        (X.fromSpecResidueField x ≫ f) (X.fromSpecResidueField x ≫ g) hf
        (by simp only [Category.assoc, hfg])
  · simp only [Category.assoc, variableChange_toBase, addMorphisms_toBase]

/-- Coordinate changes preserve the actual addition morphism on the cubic product. -/
theorem addition_variableChange [IsNoetherianRing R] [_root_.IsReduced R] [W.IsElliptic] :
    addition (C • W) ≫ variableChangeMorphism W C =
      addMorphisms W
        (pullback.fst (toBase (C • W)) (toBase (C • W)) ≫
          variableChangeMorphism W C)
        (pullback.snd (toBase (C • W)) (toBase (C • W)) ≫
          variableChangeMorphism W C)
        (by simp only [Category.assoc, variableChange_toBase,
          pullback.condition]) := by
  have : IsLocallyNoetherian (scheme (C • W)) :=
    LocallyOfFiniteType.isLocallyNoetherian (toBase (C • W))
  have : AlgebraicGeometry.IsReduced
      (pullback (toBase (C • W)) (toBase (C • W))) := inferInstance
  have h := addMorphisms_variableChange_of_isReduced W C
    (pullback.fst (toBase (C • W)) (toBase (C • W)))
    (pullback.snd (toBase (C • W)) (toBase (C • W)))
    pullback.condition
  simpa only [addMorphisms, pullback.lift_fst_snd,
    Category.id_comp] using h


/-- The coordinate change as a morphism over the coefficient base. -/
def variableChangeOver : groupModel (C • W) ⟶ groupModel W :=
  Over.homMk (variableChangeMorphism W C) (variableChange_toBase W C)

/-- The pointed coordinate-change isomorphism over the coefficient base. -/
def variableChangeOverIso : groupModel (C • W) ≅ groupModel W :=
  Over.isoMk (variableChangeIso W C) (variableChange_toBase W C)

open MonoidalCategory MonObj
instance variableChangeOverIsMonHom [IsNoetherianRing R] [_root_.IsReduced R] [W.IsElliptic] :
    IsMonHom (variableChangeOver W C) where
  one_hom := by
    apply Over.OverMorphism.ext
    exact infinity_variableChange W C
  mul_hom := by
    apply Over.OverMorphism.ext
    exact addition_variableChange W C

@[simp] theorem variableChangeOverIso_hom :
    (variableChangeOverIso W C).hom = variableChangeOver W C := by
  apply Over.OverMorphism.ext
  rfl

instance variableChangeOverIsoIsMonHom [IsNoetherianRing R] [_root_.IsReduced R] [W.IsElliptic] :
    IsMonHom (variableChangeOverIso W C).hom := by
  rw [variableChangeOverIso_hom]
  infer_instance

instance variableChangeOverIsoInvIsMonHom [IsNoetherianRing R] [_root_.IsReduced R]
    [W.IsElliptic] : IsMonHom (variableChangeOverIso W C).inv := inferInstance

end WeierstrassCurve.CubicCharts
