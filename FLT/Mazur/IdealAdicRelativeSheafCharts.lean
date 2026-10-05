/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeSheaf
public import FLT.Mazur.IdealAdicClosedGradedRestriction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

/-!
# Actual coefficient charts in the glued relative sheaf

The canonical chart maps preserve the original quotient and the original
closed coefficient comparisons. Restriction of scalars along the glued
quotient gives the sheaf of modules over the relative ring sheaf.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry TopologicalSpace
open FLT.Mazur.IdealAdicGradedClosedAction

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}}

/-- The original affine sections map canonically into the extended associated sheaf. -/
def affineRingSheafificationUnit (P : X.affineOpensᵒᵖ ⥤ CommRingCat.{u}) :
    P ⟶ (AffineBasis.inclusion X).op ⋙
      ((affineRingSheafification (X := X)).obj P).obj :=
  toSheafify (AffineBasis.topology X) P ≫
    ((AffineBasis.sheafEquivalence X CommRingCat).unitIso.hom.app
      ((presheafToSheaf (AffineBasis.topology X) CommRingCat).obj P)).hom

/-- The canonical affine chart maps commute with every original presheaf morphism. -/
lemma affineRingSheafificationUnit_naturality
    {P Q : X.affineOpensᵒᵖ ⥤ CommRingCat.{u}} (φ : P ⟶ Q) :
    φ ≫ affineRingSheafificationUnit Q =
      affineRingSheafificationUnit P ≫ whiskerLeft (AffineBasis.inclusion X).op
        ((affineRingSheafification (X := X)).map φ).hom := by
  let S := presheafToSheaf (AffineBasis.topology X) CommRingCat.{u}
  let eP := ((AffineBasis.sheafEquivalence X CommRingCat).unitIso.hom.app (S.obj P)).hom
  let eQ := ((AffineBasis.sheafEquivalence X CommRingCat).unitIso.hom.app (S.obj Q)).hom
  let ψ := whiskerLeft (AffineBasis.inclusion X).op (affineRingSheafification.map φ).hom
  have h : (S.map φ).hom ≫ eQ = eP ≫ ψ :=
    (sheafToPresheaf (AffineBasis.topology X) CommRingCat).congr_map
      ((AffineBasis.sheafEquivalence X CommRingCat).unitIso.hom.naturality (S.map φ))
  calc
    φ ≫ affineRingSheafificationUnit Q =
        (φ ≫ toSheafify (AffineBasis.topology X) Q) ≫ eQ := (Category.assoc ..).symm
    _ = (toSheafify (AffineBasis.topology X) P ≫ (S.map φ).hom) ≫ eQ :=
      congrArg (fun k ↦ k ≫ eQ) (toSheafify_naturality _ φ)
    _ = toSheafify (AffineBasis.topology X) P ≫ ((S.map φ).hom ≫ eQ) := Category.assoc ..
    _ = toSheafify (AffineBasis.topology X) P ≫ (eP ≫ ψ) :=
      congrArg (fun k ↦ toSheafify (AffineBasis.topology X) P ≫ k) h
    _ = _ := (Category.assoc ..).symm

variable [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

/-- The glued quotient retains the actual relative quotient on every affine chart. -/
lemma relativeSheafQuotient_chart :
    relativeAffineQuotient J f ≫
        affineRingSheafificationUnit (coefficientAffinePresheaf J f) =
      affineRingSheafificationUnit (relativeAffinePresheaf J f) ≫
        whiskerLeft (AffineBasis.inclusion X).op (relativeSheafQuotient J f).hom :=
  affineRingSheafificationUnit_naturality (relativeAffineQuotient J f)

/-- The actual total closed coefficients map into the glued coefficient sheaf on the basis. -/
def closedCoefficientChartMap :
    (AffineBasis.inclusion X).op ⋙ totalPresheaf (J.comap f) ⟶
      (AffineBasis.inclusion X).op ⋙ (coefficientRingSheaf J f).obj ⋙
        forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u} :=
  whiskerLeft (AffineBasis.inclusion X).op (totalPresheafIso (J.comap f)).hom ≫
    whiskerRight (affineRingSheafificationUnit (coefficientAffinePresheaf J f))
      (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u})

omit [IsLocallyNoetherian Y] [IsAffine Y] in
/-- Each homogeneous chart map uses the actual closed-to-ambient comparison. -/
lemma closedCoefficientChartMap_of (U : X.affineOpens) (n : ℕ)
    (s : ClosedPiece (J.comap f) U.1 n) :
    (closedCoefficientChartMap J f).app (.op U)
        (DirectSum.of (ClosedPiece (J.comap f) U.1) n s) =
      (affineRingSheafificationUnit (coefficientAffinePresheaf J f)).app (.op U)
        (IdealAdicGradedSections.of (J.comap f) U.1 n
          (pieceEquiv (J.comap f) U.1 n s)) := by
  change (affineRingSheafificationUnit (coefficientAffinePresheaf J f)).app (.op U)
    (totalEquiv (J.comap f) U.1 (DirectSum.of (ClosedPiece (J.comap f) U.1) n s)) = _
  rw [totalEquiv_of]

/-- The relative ring sheaf with its underlying ring category. -/
def relativeScalarSheaf : Sheaf (Opens.grothendieckTopology X) RingCat.{u} :=
  (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj (relativeRingSheaf J f)

/-- The actual coefficient ring sheaf, viewed as a module over the relative ring sheaf. -/
def relativeCoefficientModuleSheaf : SheafOfModules (relativeScalarSheaf J f) :=
  (SheafOfModules.restrictScalars
    ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map (relativeSheafQuotient J f))).obj
      (SheafOfModules.unit
        ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj (coefficientRingSheaf J f)))

/-- Module sections retain the actual underlying sections of the coefficient ring sheaf. -/
def relativeCoefficientSectionEquiv (U : X.Opensᵒᵖ) :
    (relativeCoefficientModuleSheaf J f).val.obj U ≃+
      (coefficientRingSheaf J f).obj.obj U := AddEquiv.refl _

/-- The global module action is multiplication through the actual glued quotient. -/
lemma relativeCoefficientModuleSheaf_smul (U : X.Opensᵒᵖ)
    (r : (relativeScalarSheaf J f).obj.obj U)
    (s : (relativeCoefficientModuleSheaf J f).val.obj U) :
    relativeCoefficientSectionEquiv J f U (r • s) =
      (relativeSheafQuotient J f).hom.app U r * relativeCoefficientSectionEquiv J f U s := rfl

end FLT.Mazur.IdealAdicGradedPullback
