/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTensorIntegerClosedImmersion
public import FLT.Mazur.FiniteIntersectionDiagonalCoordinates

/-!
# Closed products at a common intersection coefficient stage

All pairs use one coefficient instance for each diagram object, including
objects repeated as left charts, right charts, and union intersections.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u v

/-- Enlarge a fixed intersection model so all overlap product maps are closed. -/
theorem exists_intersection_model_closed_products {A : Type u} [CommRing A]
    {X : Scheme.{u}} {ι : Type v} [Finite ι] (U : ι → X.Opens)
    (p : X ⟶ Spec (.of A)) [X.IsSeparated] (hU : ∀ i, IsAffineOpen (U i))
    (n m : NonemptyChartSet ι → ℕ)
    (P : ∀ a, Algebra.Presentation A ((finiteIntersectionSectionDiagram U p).obj a)
      (Fin (n a)) (Fin (m a)))
    (R : Subalgebra ℤ A) [Algebra.FiniteType ℤ R] [∀ a, (P a).HasCoeffs R]
    (ψ : ∀ {a b}, (a ⟶ b) →
      ((P a).ModelOfHasCoeffs R →ₐ[R] (P b).ModelOfHasCoeffs R))
    (hrec : ∀ {a b} (f : a ⟶ b) x, (P b).tensorModelOfHasCoeffsEquiv R (1 ⊗ₜ ψ f x) =
      ((finiteIntersectionSectionDiagram U p).map f).hom
        ((P a).tensorModelOfHasCoeffsEquiv R (1 ⊗ₜ x)))
    (s : Set A) (hs : s.Finite) :
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ s ⊆ S ∧
      ∃ h : R ≤ S, ∃ _hP : ∀ a, (P a).HasCoeffs S,
        ∀ a b, IsClosedImmersion (Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.productMap
            (integerModelTransportHom (P a) (P (unionChartSet a b)) h
              (ψ (homOfLE (le_unionChartSet_left a b))))
            (integerModelTransportHom (P b) (P (unionChartSet a b)) h
              (ψ (homOfLE (le_unionChartSet_right a b))))).toRingHom)) := by
  let C := finiteIntersectionSectionDiagram U p
  let J := NonemptyChartSet ι × NonemptyChartSet ι
  let : ∀ q : J, IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.productMap
        (C.map (homOfLE (le_unionChartSet_left q.1 q.2))).hom
        (C.map (homOfLE (le_unionChartSet_right q.1 q.2))).hom).toRingHom)) :=
    fun q ↦ finiteIntersectionSectionDiagram_product_closedImmersion U p hU q.1 q.2
  obtain ⟨S, hS, hsS, h, _, _, _, hc⟩ := exists_finite_tensor_integer_closedImmersions
    (fun q : J ↦ ↥(C.obj q.1)) (fun q : J ↦ ↥(C.obj q.2))
    (fun q : J ↦ ↥(C.obj (unionChartSet q.1 q.2)))
    (fun q ↦ n q.1) (fun q ↦ m q.1) (fun q ↦ n q.2) (fun q ↦ m q.2)
    (fun q ↦ n (unionChartSet q.1 q.2)) (fun q ↦ m (unionChartSet q.1 q.2))
    (fun q ↦ P q.1) (fun q ↦ P q.2) (fun q ↦ P (unionChartSet q.1 q.2)) R
    (fun q ↦ ψ (homOfLE (le_unionChartSet_left q.1 q.2)))
    (fun q ↦ ψ (homOfLE (le_unionChartSet_right q.1 q.2)))
    (fun q ↦ (C.map (homOfLE (le_unionChartSet_left q.1 q.2))).hom)
    (fun q ↦ (C.map (homOfLE (le_unionChartSet_right q.1 q.2))).hom)
    (fun _ ↦ hrec _) (fun _ ↦ hrec _) s hs
  let hP : ∀ a, (P a).HasCoeffs S := fun a ↦ integerModel_hasCoeffs_mono (P a) h
  exact ⟨S, hS, hsS, h, hP, fun a b ↦ hc (a, b)⟩

end FLT.Mazur.Approximation
