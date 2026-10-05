/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteIntersectionIntegerModel
public import FLT.Mazur.IntersectionModelClosedProducts
public import FLT.Mazur.IntegerModelPullbackTransport

/-!
# Intersection coefficient models with closed diagonals

Enlarge the fixed model to close all overlap product maps while retaining
its identity, composition, recovery, open-immersion, and union-square laws.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u v

/-- Descend actual intersection coordinates with closed overlap products. -/
theorem exists_finite_intersection_closed_model {A : Type u} [CommRing A]
    {X : Scheme.{u}} {ι : Type v} [Finite ι] (U : ι → X.Opens)
    (p : X ⟶ Spec (.of A)) [X.IsSeparated] [LocallyOfFinitePresentation p]
    (hU : ∀ i, IsAffineOpen (U i)) (s : Set A) (hs : s.Finite) :
    let C := finiteIntersectionSectionDiagram U p
    ∃ n m : NonemptyChartSet ι → ℕ,
      ∃ P : ∀ a, Algebra.Presentation A (C.obj a) (Fin (n a)) (Fin (m a)),
        ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ s ⊆ S ∧
          ∃ _hP : ∀ a, (P a).HasCoeffs S,
            ∃ ψ : ∀ {a b}, (a ⟶ b) →
              ((P a).ModelOfHasCoeffs S →ₐ[S] (P b).ModelOfHasCoeffs S),
            (∀ a, ψ (𝟙 a) = AlgHom.id S _) ∧
            (∀ {a b c} (f : a ⟶ b) (g : b ⟶ c), ψ (f ≫ g) = (ψ g).comp (ψ f)) ∧
            (∀ {a b} (f : a ⟶ b) x, (P b).tensorModelOfHasCoeffsEquiv S (1 ⊗ₜ ψ f x) =
              (C.map f).hom ((P a).tensorModelOfHasCoeffsEquiv S (1 ⊗ₜ x))) ∧
            (∀ a b (f : a ⟶ b),
              IsOpenImmersion (Spec.map (CommRingCat.ofHom (ψ f).toRingHom))) ∧
            (∀ a b, IsClosedImmersion (Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.productMap
                (ψ (homOfLE (le_unionChartSet_left a b)))
                (ψ (homOfLE (le_unionChartSet_right a b)))).toRingHom))) ∧
            ∀ q : IntersectionSquareIndex ι,
              IsPullback
                (Spec.map (CommRingCat.ofHom
                  (ψ (homOfLE (le_unionChartSet_left q.val.2.1 q.val.2.2))).toRingHom))
                (Spec.map (CommRingCat.ofHom
                  (ψ (homOfLE (le_unionChartSet_right q.val.2.1 q.val.2.2))).toRingHom))
                (Spec.map (CommRingCat.ofHom (ψ (homOfLE q.property.1)).toRingHom))
                (Spec.map (CommRingCat.ofHom (ψ (homOfLE q.property.2)).toRingHom)) := by
  let C := finiteIntersectionSectionDiagram U p
  obtain ⟨n, m, P, R, hR, _, hPR, ψ₀, hid₀, hcomp₀, hrec₀, hopen₀, hp₀⟩ :=
    exists_finite_intersection_integer_model U p hU ∅ Set.finite_empty
  let := hR
  let := hPR
  obtain ⟨S, hS, hsS, hRS, hP, hc⟩ :=
    exists_intersection_model_closed_products U p hU n m P R ψ₀ hrec₀ s hs
  let := hP
  let ψ : ∀ {a b}, (a ⟶ b) →
      ((P a).ModelOfHasCoeffs S →ₐ[S] (P b).ModelOfHasCoeffs S) :=
    fun {a b} f ↦ integerModelTransportHom (P a) (P b) hRS (ψ₀ f)
  have hid a : ψ (𝟙 a) = AlgHom.id S _ := by
    simp only [ψ, hid₀, integerModelTransportHom_id]
  have hcomp {a b c} (f : a ⟶ b) (k : b ⟶ c) : ψ (f ≫ k) = (ψ k).comp (ψ f) := by
    simp only [ψ, hcomp₀, integerModelTransportHom_comp]
  have hrec {a b} (f : a ⟶ b) x :
      (P b).tensorModelOfHasCoeffsEquiv S (1 ⊗ₜ ψ f x) =
        (C.map f).hom ((P a).tensorModelOfHasCoeffsEquiv S (1 ⊗ₜ x)) :=
    integerModelTransportHom_recovery (P a) (P b) hRS (ψ₀ f) (C.map f).hom (hrec₀ f) x
  have hopen a b (f : a ⟶ b) :
      IsOpenImmersion (Spec.map (CommRingCat.ofHom (ψ f).toRingHom)) :=
    integerModelTransportHom_isOpenImmersion (P a) (P b) hRS (ψ₀ f) (hopen₀ a b f)
  have hp (q : IntersectionSquareIndex ι) :
      IsPullback
        (Spec.map (CommRingCat.ofHom
          (ψ (homOfLE (le_unionChartSet_left q.val.2.1 q.val.2.2))).toRingHom))
        (Spec.map (CommRingCat.ofHom
          (ψ (homOfLE (le_unionChartSet_right q.val.2.1 q.val.2.2))).toRingHom))
        (Spec.map (CommRingCat.ofHom (ψ (homOfLE q.property.1)).toRingHom))
        (Spec.map (CommRingCat.ofHom (ψ (homOfLE q.property.2)).toRingHom)) :=
    integerModelTransportHom_preserves_pullback (P q.val.1) (P q.val.2.1) (P q.val.2.2)
      (P (unionChartSet q.val.2.1 q.val.2.2)) hRS _ _ _ _ (hp₀ q)
  exact ⟨n, m, P, S, hS, hsS, hP, ψ, hid, hcomp, hrec, hopen, hc, hp⟩

end FLT.Mazur.Approximation
