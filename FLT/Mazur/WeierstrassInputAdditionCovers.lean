/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAffineAdditionTransport
public import FLT.Mazur.WeierstrassMixedProductCover

/-!
# Full input-product covers carrying local addition morphisms

In good reduction, refine the affine member of each input-product cover by
the four transported addition domains. All remaining members already carry
regular addition. This constructs local maps everywhere on the Y/Z products;
identifying them on intersections and gluing them remains a separate step.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open AlgebraicGeometry CategoryTheory

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- Refine only the affine member of the complete Y-product cover. -/
def yProductAdditionRefinement (i : YProductCoverIndex) :
    (Spec (yProductCoverRing W i)).OpenCover :=
  match i with
  | .affine => affineOverlapAdditionCover W 1 1 hΔ
  | .polynomial => Scheme.coverOfIsIso (𝟙 _)
  | .infinity => Scheme.coverOfIsIso (𝟙 _)

/-- A six-member cover carrying regular addition at every Y-chart input pair. -/
def yProductAdditionCover : (Spec (CommRingCat.of (ChartProduct W 1 1))).OpenCover :=
  (yProductOpenCover W).bind (yProductAdditionRefinement W hΔ)

/-- The output coordinate chart of each regular addition member. -/
def yProductAdditionOutput (i : (yProductAdditionCover W hΔ).I₀) : Fin 3 :=
  match i with
  | ⟨.affine, t⟩ => additionChartOutput t
  | ⟨.polynomial, _⟩ => 2
  | ⟨.infinity, _⟩ => 1

/-- Actual regular addition morphisms on every member of the full Y-product cover. -/
def yProductAdditionSpec (i : (yProductAdditionCover W hΔ).I₀) :
    (yProductAdditionCover W hΔ).X i ⟶
      Spec (CommRingCat.of (Coordinate W (yProductAdditionOutput W hΔ i))) :=
  match i with
  | ⟨.affine, t⟩ => affineOverlapAdditionSpec W 1 1 hΔ t
  | ⟨.polynomial, _⟩ => Spec.map (CommRingCat.ofHom (projectiveAdditionChart W 1 1 2).toRingHom)
  | ⟨.infinity, _⟩ => infinityAdditionSpec W

variable (j k : Fin 3)

/-- Refine the affine overlap in a product with at least one affine input. -/
def mixedProductAdditionRefinement (b : Bool) :
    (Spec (mixedProductCoverRing W j k b)).OpenCover :=
  match b with
  | true => affineOverlapAdditionCover W j k hΔ
  | false => Scheme.coverOfIsIso (𝟙 _)

/-- The five regular addition domains cover each mixed Y/Z input product. -/
def mixedProductAdditionCover (hj : j = 1 ∨ j = 2) (hk : k = 1 ∨ k = 2)
    (ha : j = 2 ∨ k = 2) : (Spec (CommRingCat.of (ChartProduct W j k))).OpenCover :=
  (mixedProductOpenCover W j k hj hk ha).bind (mixedProductAdditionRefinement W hΔ j k)

/-- The output chart of each member of a mixed product cover. -/
def mixedProductAdditionOutput (hj : j = 1 ∨ j = 2) (hk : k = 1 ∨ k = 2)
    (ha : j = 2 ∨ k = 2) (i : (mixedProductAdditionCover W hΔ j k hj hk ha).I₀) : Fin 3 :=
  match i with
  | ⟨true, t⟩ => additionChartOutput t
  | ⟨false, _⟩ => 2

/-- Actual addition morphisms on every open of a mixed product cover. -/
def mixedProductAdditionSpec (hj : j = 1 ∨ j = 2) (hk : k = 1 ∨ k = 2)
    (ha : j = 2 ∨ k = 2) (i : (mixedProductAdditionCover W hΔ j k hj hk ha).I₀) :
    (mixedProductAdditionCover W hΔ j k hj hk ha).X i ⟶
      Spec (CommRingCat.of (Coordinate W (mixedProductAdditionOutput W hΔ j k hj hk ha i))) :=
  match i with
  | ⟨true, t⟩ => affineOverlapAdditionSpec W j k hΔ t
  | ⟨false, _⟩ => Spec.map (CommRingCat.ofHom (projectiveAdditionChart W j k 2).toRingHom)

end FLT.Mazur.WeierstrassIntegralChart
