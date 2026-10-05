/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ChowAffineBaseChartData
public import FLT.Mazur.ChowProjectiveProduct
public import FLT.Mazur.ProjectiveSpaceProper

/-!
# The finite projective product for affine-base Chow charts

Finite relative products of proper schemes are constructed by iterated
pullbacks, starting with the base for the empty family. The construction
includes its universal maps and their uniqueness. Applied to the projective
spaces of the affine charts, it gives the common-open tuple over the affine base.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.Chow.AffineBase

namespace ChartData

variable {R : CommRingCat.{u}} {X : Scheme.{u}} {f : X ⟶ Spec R} (D : ChartData f)

/-- Enumerate the actual chart projective spaces and construct their relative product. -/
def projectiveProductData :=
  finProperProduct (Spec R) (Fintype.card D.Index)
    (fun j ↦ ProjectiveSpace.space R
      (Fin (D.dimension ((Fintype.equivFin D.Index).symm j) + 1)))
    (fun j ↦ ProjectiveSpace.baseProjection R
      (Fin (D.dimension ((Fintype.equivFin D.Index).symm j) + 1)))
    (fun _ ↦ inferInstance)

/-- The product of the chart projective spaces over the original affine base. -/
def projectiveProduct : Scheme.{u} := D.projectiveProductData.obj

/-- The structure map of the finite relative projective product. -/
def projectiveProductProjection : D.projectiveProduct ⟶ Spec R :=
  D.projectiveProductData.base

instance projectiveProductProjection_isProper : IsProper D.projectiveProductProjection :=
  D.projectiveProductData.proper

/-- The projection to a chart's original projective space. -/
def projectiveProductπ (i : D.Index) :
    D.projectiveProduct ⟶ ProjectiveSpace.space R (Fin (D.dimension i + 1)) :=
  D.projectiveProductData.π (Fintype.equivFin D.Index i) ≫ eqToHom (by simp)

/-- Every coordinate projection is over the original base. -/
@[reassoc (attr := simp)]
lemma projectiveProductπ_baseProjection (i : D.Index) :
    D.projectiveProductπ i ≫ ProjectiveSpace.baseProjection R (Fin (D.dimension i + 1)) =
      D.projectiveProductProjection := by
  rw [projectiveProductπ, Category.assoc, ← eqToHom_naturality
    (fun i ↦ ProjectiveSpace.baseProjection R (Fin (D.dimension i + 1)))
    ((Fintype.equivFin D.Index).symm_apply_apply i)]
  simpa only [eqToHom_refl, Category.comp_id, projectiveProductProjection,
    projectiveProduct] using
    D.projectiveProductData.π_base (Fintype.equivFin D.Index i)

/-- The universal tuple into the finite projective product. -/
def projectiveProductLift {T : Scheme.{u}} (b : T ⟶ Spec R)
    (g : ∀ i, T ⟶ ProjectiveSpace.space R (Fin (D.dimension i + 1)))
    (w : ∀ i, g i ≫ ProjectiveSpace.baseProjection R (Fin (D.dimension i + 1)) = b) :
    T ⟶ D.projectiveProduct :=
  D.projectiveProductData.lift b (fun j ↦ g ((Fintype.equivFin D.Index).symm j))
    (fun j ↦ w ((Fintype.equivFin D.Index).symm j))

@[reassoc (attr := simp)]
lemma projectiveProductLift_projection {T : Scheme.{u}} (b : T ⟶ Spec R)
    (g : ∀ i, T ⟶ ProjectiveSpace.space R (Fin (D.dimension i + 1)))
    (w : ∀ i, g i ≫ ProjectiveSpace.baseProjection R (Fin (D.dimension i + 1)) = b) :
    D.projectiveProductLift b g w ≫ D.projectiveProductProjection = b :=
  D.projectiveProductData.lift_base _ _ _

@[reassoc (attr := simp)]
lemma projectiveProductLift_π {T : Scheme.{u}} (b : T ⟶ Spec R)
    (g : ∀ i, T ⟶ ProjectiveSpace.space R (Fin (D.dimension i + 1)))
    (w : ∀ i, g i ≫ ProjectiveSpace.baseProjection R (Fin (D.dimension i + 1)) = b)
    (i : D.Index) : D.projectiveProductLift b g w ≫ D.projectiveProductπ i = g i := by
  unfold projectiveProductLift projectiveProductπ
  rw [← Category.assoc, ProperRelativeProduct.lift_π]
  simp

/-- The base and coordinate maps determine a map to the product uniquely. -/
@[ext]
lemma projectiveProduct_hom_ext {T : Scheme.{u}} (r s : T ⟶ D.projectiveProduct)
    (hb : r ≫ D.projectiveProductProjection = s ≫ D.projectiveProductProjection)
    (hπ : ∀ i, r ≫ D.projectiveProductπ i = s ≫ D.projectiveProductπ i) : r = s := by
  apply D.projectiveProductData.hom_ext r s hb
  intro j
  have h := hπ ((Fintype.equivFin D.Index).symm j)
  simp only [projectiveProductπ, ← Category.assoc, cancel_mono] at h
  rw [Equiv.apply_symm_apply] at h
  exact h

/-- An empty family has the base spectrum as its relative product. -/
def projectiveProductEmptyIso [IsEmpty D.Index] : D.projectiveProduct ≅ Spec R := by
  have : IsEmpty (Fin (Fintype.card D.Index)) := by
    simpa only [Fintype.card_eq_zero] using (inferInstance : IsEmpty (Fin 0))
  exact D.projectiveProductData.emptyIso

/-- The common open maps to the product by all its projective component maps. -/
def commonToProduct : D.common.toScheme ⟶ D.projectiveProduct :=
  D.projectiveProductLift (D.common.ι ≫ f) D.commonToProjective
    D.commonToProjective_baseProjection

/-- The tuple has exactly the prescribed chart components. -/
@[reassoc (attr := simp)]
lemma commonToProduct_π (i : D.Index) :
    D.commonToProduct ≫ D.projectiveProductπ i = D.commonToProjective i :=
  D.projectiveProductLift_π _ _ _ i

/-- The tuple retains the structure morphism of the original common open. -/
@[reassoc (attr := simp)]
lemma commonToProduct_projection :
    D.commonToProduct ≫ D.projectiveProductProjection = D.common.ι ≫ f :=
  D.projectiveProductLift_projection _ _ _

end ChartData

end FLT.Mazur.Chow.AffineBase
