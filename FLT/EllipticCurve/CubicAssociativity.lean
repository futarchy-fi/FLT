/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicFieldPointClassification
public import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-! # Associativity of cubic addition on reduced sources -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Sum of two morphisms into the cubic with the same coefficient-base map. -/
def addMorphisms [W.IsElliptic] {X : Scheme.{u}} (f g : X ⟶ scheme W)
    (h : f ≫ toBase W = g ≫ toBase W) : X ⟶ scheme W :=
  pullback.lift f g h ≫ addition W

@[reassoc (attr := simp)] theorem addMorphisms_toBase [W.IsElliptic] {X : Scheme.{u}}
    (f g : X ⟶ scheme W) (h : f ≫ toBase W = g ≫ toBase W) :
    addMorphisms W f g h ≫ toBase W = f ≫ toBase W := by
  simp [addMorphisms]

theorem addMorphisms_precomp [W.IsElliptic] {X Y : Scheme.{u}}
    (f g : X ⟶ scheme W) (h : f ≫ toBase W = g ≫ toBase W) (t : Y ⟶ X) :
    t ≫ addMorphisms W f g h =
      addMorphisms W (t ≫ f) (t ≫ g) (by simp only [Category.assoc, h]) := by
  unfold addMorphisms
  rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext <;> simp

theorem addMorphisms_fieldPoints [W.IsElliptic]
    {K : Type u} [Field K] [Algebra R K] [DecidableEq K]
    (P Q : (W.map (algebraMap R K)).toAffine.Point)
    (h : fieldPointMorphism W P ≫ toBase W = fieldPointMorphism W Q ≫ toBase W) :
    addMorphisms W (fieldPointMorphism W P) (fieldPointMorphism W Q) h =
      fieldPointMorphism W (P + Q) :=
  fieldPointPair_add W P Q

theorem addMorphisms_assoc_field [W.IsElliptic]
    {K : Type u} [Field K] [Algebra R K]
    (f g h : Spec (.of K) ⟶ scheme W)
    (hf : f ≫ toBase W = Spec.map (CommRingCat.ofHom (algebraMap R K)))
    (hfg : f ≫ toBase W = g ≫ toBase W) (hfh : f ≫ toBase W = h ≫ toBase W) :
    addMorphisms W (addMorphisms W f g hfg) h (by simp [hfh]) =
      addMorphisms W f (addMorphisms W g h (hfg.symm.trans hfh)) (by simp [hfg]) := by
  classical
  obtain ⟨P, rfl⟩ := fieldPointMorphism_surjective W f hf
  obtain ⟨Q, rfl⟩ := fieldPointMorphism_surjective W g (hfg.symm.trans hf)
  obtain ⟨T, rfl⟩ := fieldPointMorphism_surjective W h (hfh.symm.trans hf)
  simp only [addMorphisms_fieldPoints, add_assoc]

/-- Associativity holds for maps from every reduced source scheme. The residue-field
comparison uses the actual classical group law and exhausts all field-valued points. -/
theorem addMorphisms_assoc_of_isReduced [W.IsElliptic]
    {X : Scheme.{u}} [AlgebraicGeometry.IsReduced X]
    (f g h : X ⟶ scheme W)
    (hfg : f ≫ toBase W = g ≫ toBase W) (hfh : f ≫ toBase W = h ≫ toBase W) :
    addMorphisms W (addMorphisms W f g hfg) h (by simp [hfh]) =
      addMorphisms W f (addMorphisms W g h (hfg.symm.trans hfh)) (by simp [hfg]) := by
  apply ext_of_fromSpecResidueField_eq _ _ (toBase W) Set.univ dense_univ
  · intro x _
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.fromSpecResidueField x ≫ f ≫ toBase W)
    let K : Type u := IsLocalRing.ResidueField (X.presheaf.stalk x)
    let : Algebra R K := φ.hom.toAlgebra
    have hf : (X.fromSpecResidueField x ≫ f) ≫ toBase W =
        Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
      change (X.fromSpecResidueField x ≫ f) ≫ toBase W = Spec.map φ
      simpa only [Category.assoc] using hφ.symm
    simp only [addMorphisms_precomp]
    exact addMorphisms_assoc_field W (K := K) _ _ _ hf
      (by simp only [Category.assoc, hfg]) (by simp only [Category.assoc, hfh])
  · simp

/-- Every geometric fiber of the cubic is integral, including singular fibers. -/
instance toBase_geometricallyIntegral : GeometricallyIntegral (toBase W) := by
  let : ObjectProperty.IsClosedUnderIsomorphisms
      (fun X : Scheme.{u} ↦ AlgebraicGeometry.IsIntegral X) :=
    ⟨fun e _ ↦ AlgebraicGeometry.IsIntegral.of_isIso e.hom⟩
  constructor
  apply (geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := fun X : Scheme.{u} ↦ AlgebraicGeometry.IsIntegral X) (R := R) (f := toBase W)).mpr
  intro K _ _
  exact AlgebraicGeometry.IsIntegral.of_isIso (baseChangeIso W K).hom

/-- Over a reduced noetherian coefficient ring, the smooth cubic is reduced. -/
instance scheme_isReduced_of_base [IsNoetherianRing R] [_root_.IsReduced R] [W.IsElliptic] :
    AlgebraicGeometry.IsReduced (scheme W) :=
  GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian (toBase W)

/-- The structure morphism of the product of two copies of the cubic. -/
def pairToBase : pullback (toBase W) (toBase W) ⟶ Spec (.of R) :=
  pullback.fst (toBase W) (toBase W) ≫ toBase W

/-- The product of three copies, parenthesized as the first pair and the third point. -/
abbrev TripleProduct := pullback (pairToBase W) (toBase W)

/-- First projection from the triple product. -/
def tripleFirst : TripleProduct W ⟶ scheme W :=
  pullback.fst (pairToBase W) (toBase W) ≫ pullback.fst (toBase W) (toBase W)

/-- Second projection from the triple product. -/
def tripleSecond : TripleProduct W ⟶ scheme W :=
  pullback.fst (pairToBase W) (toBase W) ≫ pullback.snd (toBase W) (toBase W)

/-- Third projection from the triple product. -/
def tripleThird : TripleProduct W ⟶ scheme W :=
  pullback.snd (pairToBase W) (toBase W)

theorem tripleFirst_toBase_eq_second :
    tripleFirst W ≫ toBase W = tripleSecond W ≫ toBase W := by
  simp only [tripleFirst, tripleSecond, Category.assoc, pullback.condition]

theorem tripleFirst_toBase_eq_third :
    tripleFirst W ≫ toBase W = tripleThird W ≫ toBase W := by
  simpa only [tripleFirst, tripleThird, Category.assoc, pairToBase] using
    (pullback.condition (f := pairToBase W) (g := toBase W))

/-- Associativity as equality of the two morphisms out of the actual triple product,
over every reduced noetherian coefficient ring. -/
theorem addition_assoc [IsNoetherianRing R] [_root_.IsReduced R] [W.IsElliptic] :
    addMorphisms W
        (addMorphisms W (tripleFirst W) (tripleSecond W) (tripleFirst_toBase_eq_second W))
        (tripleThird W) (by simp [tripleFirst_toBase_eq_third]) =
      addMorphisms W (tripleFirst W)
        (addMorphisms W (tripleSecond W) (tripleThird W)
          ((tripleFirst_toBase_eq_second W).symm.trans (tripleFirst_toBase_eq_third W)))
        (by simp [tripleFirst_toBase_eq_second]) := by
  have : IsLocallyNoetherian (scheme W) :=
    LocallyOfFiniteType.isLocallyNoetherian (toBase W)
  have : AlgebraicGeometry.IsReduced (pullback (toBase W) (toBase W)) := inferInstance
  have : IsLocallyNoetherian (pullback (toBase W) (toBase W)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst (toBase W) (toBase W))
  have : AlgebraicGeometry.IsReduced (TripleProduct W) := inferInstance
  exact addMorphisms_assoc_of_isReduced W _ _ _
    (tripleFirst_toBase_eq_second W) (tripleFirst_toBase_eq_third W)

/-- Associativity for arbitrary source schemes over a reduced noetherian base.
The source itself may be nonreduced: pull back the equality on the triple product. -/
theorem addMorphisms_assoc [IsNoetherianRing R] [_root_.IsReduced R] [W.IsElliptic]
    {X : Scheme.{u}} (f g h : X ⟶ scheme W)
    (hfg : f ≫ toBase W = g ≫ toBase W) (hfh : f ≫ toBase W = h ≫ toBase W) :
    addMorphisms W (addMorphisms W f g hfg) h (by simp [hfh]) =
      addMorphisms W f (addMorphisms W g h (hfg.symm.trans hfh)) (by simp [hfg]) := by
  let t : X ⟶ TripleProduct W :=
    pullback.lift (pullback.lift f g hfg) h (by simp [pairToBase, hfh])
  have h₁ : t ≫ tripleFirst W = f := by simp [t, tripleFirst]
  have h₂ : t ≫ tripleSecond W = g := by simp [t, tripleSecond]
  have h₃ : t ≫ tripleThird W = h := by simp [t, tripleThird]
  have hh := congrArg (fun k ↦ t ≫ k) (addition_assoc W)
  simpa only [addMorphisms_precomp, h₁, h₂, h₃] using hh

end WeierstrassCurve.CubicCharts
