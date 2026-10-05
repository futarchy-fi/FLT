/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteIntersectionCoordinateSquares
public import FLT.Mazur.FiniteAffineAtlasDiagramDescent

/-!
# Integer models of actual finite intersection diagrams

For affine opens in a separated scheme locally of finite presentation over
`Spec A`, construct a common finite-type integer coefficient model of their
section algebras. All restriction maps, diagram equations, open immersions,
and union squares descend together. The finite presentations are derived
from the geometric hypotheses, rather than supplied as extra inputs.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u v

/-- A union square with a specified common intersection below both label sets. -/
abbrev IntersectionSquareIndex (ι : Type v) :=
  {q : NonemptyChartSet ι × NonemptyChartSet ι × NonemptyChartSet ι //
    q.1 ≤ q.2.1 ∧ q.1 ≤ q.2.2}

/-- Construct models of the actual section diagram, retaining all union squares. -/
theorem exists_finite_intersection_integer_model {A : Type u} [CommRing A]
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
            ∀ q : IntersectionSquareIndex ι,
              IsPullback
                (Spec.map (CommRingCat.ofHom
                  (ψ (homOfLE (le_unionChartSet_left q.val.2.1 q.val.2.2))).toRingHom))
                (Spec.map (CommRingCat.ofHom
                  (ψ (homOfLE (le_unionChartSet_right q.val.2.1 q.val.2.2))).toRingHom))
                (Spec.map (CommRingCat.ofHom (ψ (homOfLE q.property.1)).toRingHom))
                (Spec.map (CommRingCat.ofHom (ψ (homOfLE q.property.2)).toRingHom)) := by
  let C := finiteIntersectionSectionDiagram U p
  obtain ⟨n, m, ⟨P⟩⟩ := finiteIntersectionSectionDiagram_presentations U p hU
  refine ⟨n, m, P, ?_⟩
  let φ := fun {a b} (f : a ⟶ b) ↦ (C.map f).hom
  have hid : ∀ a, φ (𝟙 a) = AlgHom.id A _ := by
    intro a
    simp [φ]
  have hcomp : ∀ {a b c} (f : a ⟶ b) (g : b ⟶ c),
      φ (f ≫ g) = (φ g).comp (φ f) := by
    intro a b c f g
    simp [φ]
  let hopen : ∀ a b (f : a ⟶ b),
      IsOpenImmersion (Spec.map (CommRingCat.ofHom (φ f).toRingHom)) :=
    fun _ _ f ↦ finiteIntersectionSectionDiagram_map_isOpenImmersion U p hU f
  exact exists_finite_affine_atlas_diagram_model (fun a ↦ ↥(C.obj a)) n m P φ hid hcomp
    (fun q : IntersectionSquareIndex ι ↦ q.val.1)
    (fun q ↦ q.val.2.1) (fun q ↦ q.val.2.2)
    (fun q ↦ unionChartSet q.val.2.1 q.val.2.2)
    (fun q ↦ homOfLE q.property.1) (fun q ↦ homOfLE q.property.2)
    (fun q ↦ homOfLE (le_unionChartSet_left q.val.2.1 q.val.2.2))
    (fun q ↦ homOfLE (le_unionChartSet_right q.val.2.1 q.val.2.2))
    (fun q ↦ finiteIntersectionSectionDiagram_isPullback U p hU _ _ _
      q.property.1 q.property.2) s hs

end FLT.Mazur.Approximation
