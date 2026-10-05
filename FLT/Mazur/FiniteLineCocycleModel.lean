/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteIntersectionCocycleModel
public import FLT.Mazur.LineTrivializationCocycleRecovery

/-!
# Finite coefficient models of genuine line transition data

Compactness gives a finite affine trivializing cover. Its actual transition
cocycle recovers the original sheaf and descends to a finite-type integer
base together with the coordinate atlas. This theorem does not yet claim
that the descended units have been glued to a sheaf on the model scheme.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

/-- A finite trivializing atlas and its genuine cocycle descend over the integers. -/
theorem exists_finite_line_cocycle_model {A : Type u} [CommRing A]
    {X : Scheme.{u}} [CompactSpace X] [X.IsSeparated]
    (p : X ⟶ Spec (.of A)) [LocallyOfFinitePresentation p]
    (L : X.Modules) (hL : FLT.Mazur.FCurve.LocallyFreeRankOne L)
    (s : Set A) (hs : s.Finite) :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → X.Opens),
      (∀ i, IsAffineOpen (U i)) ∧ iSup U = ⊤ ∧
      ∃ g : FLT.Mazur.FCurve.ModuleSheafUnitCocycle.Cocycle U,
        Nonempty (g.sheaf ≅ L) ∧
    let C := finiteIntersectionSectionDiagram U p
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ s ⊆ S ∧
      ∃ D : NonemptyChartSet ι ⥤ CommAlgCat S,
        ∃ e : ∀ a, A ⊗[S] D.obj a ≃ₐ[A] C.obj a,
          (∀ {a b} (f : a ⟶ b), (e b).toAlgHom.comp
              (affineScalarExtensionHom (S := A) (D.map f).hom) =
            (C.map f).hom.comp (e a).toAlgHom) ∧
          ∃ _hopen : ∀ a b (f : a ⟶ b),
            IsOpenImmersion (Spec.map (CommRingCat.ofHom (D.map f).hom.toRingHom)),
          ∃ _hp : ∀ (r a b : NonemptyChartSet ι) (hra : r ≤ a) (hrb : r ≤ b),
            IsPullback
              (Spec.map (CommRingCat.ofHom
                (D.map (homOfLE (le_unionChartSet_left a b))).hom.toRingHom))
              (Spec.map (CommRingCat.ofHom
                (D.map (homOfLE (le_unionChartSet_right a b))).hom.toRingHom))
              (Spec.map (CommRingCat.ofHom (D.map (homOfLE hra)).hom.toRingHom))
              (Spec.map (CommRingCat.ofHom (D.map (homOfLE hrb)).hom.toRingHom)),
            ∃ y : ∀ a, IntersectionPair a → (D.obj a)ˣ,
              (∀ a k, e a (1 ⊗ₜ (y a k : D.obj a)) =
                (finiteIntersectionCocycleUnit U p g a k : C.obj a)) ∧
              (∀ {a b} (f : a ⟶ b) k, (D.map f).hom (y a k) =
                (y b (intersectionPairMap f k) : D.obj b)) ∧
              ∀ a (k : IntersectionTriple a),
                y a (k.1, k.2.1) * y a (k.2.1, k.2.2) = y a (k.1, k.2.2) := by
  classical
  obtain ⟨ι, hι, U, hU, he, hcover⟩ := hL.finite_affine_trivializing_cover
  let := hι
  let e := fun i ↦ (he i).some
  let g := FLT.Mazur.FCurve.lineTrivializationCocycle e
  refine ⟨ι, hι, U, hU, hcover, g,
    ⟨FLT.Mazur.FCurve.lineTrivializationCocycleIso e hcover⟩, ?_⟩
  exact exists_finite_intersection_cocycle_model U p hU g s hs

end FLT.Mazur.Approximation
