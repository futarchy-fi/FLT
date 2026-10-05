/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineIntersectionDiagramGluing
public import FLT.Mazur.FiniteIntersectionIntegerModel

/-!
# Constructing the glued integer model of an intersection atlas

The model supplied by algebraic descent is packaged as a functor and glued
over its coefficient ring. Recovery retains every scalar-extended arrow,
not just the objects. This constructs the model gluing; identifying its
base change with the original scheme still requires compatibility of gluing
with scalar extension.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u v

/-- Construct a glued model, retaining the full scalar-extended coordinate diagram. -/
theorem exists_finite_intersection_glued_model {A : Type u} [CommRing A]
    {X : Scheme.{u}} {ι : Type v} [Finite ι] (U : ι → X.Opens)
    (p : X ⟶ Spec (.of A)) [X.IsSeparated] [LocallyOfFinitePresentation p]
    (hU : ∀ i, IsAffineOpen (U i)) (s : Set A) (hs : s.Finite) :
    let C := finiteIntersectionSectionDiagram U p
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ s ⊆ S ∧
      ∃ D : NonemptyChartSet ι ⥤ CommAlgCat S,
        ∃ e : ∀ a, A ⊗[S] D.obj a ≃ₐ[A] C.obj a,
          (∀ {a b} (f : a ⟶ b), (e b).toAlgHom.comp
              (affineScalarExtensionHom (S := A) (D.map f).hom) =
            (C.map f).hom.comp (e a).toAlgHom) ∧
          ∃ _hopen : ∀ a b (f : a ⟶ b),
            IsOpenImmersion (Spec.map (CommRingCat.ofHom (D.map f).hom.toRingHom)),
          ∃ hp : ∀ (r a b : NonemptyChartSet ι) (hra : r ≤ a) (hrb : r ≤ b),
            IsPullback
              (Spec.map (CommRingCat.ofHom
                (D.map (homOfLE (le_unionChartSet_left a b))).hom.toRingHom))
              (Spec.map (CommRingCat.ofHom
                (D.map (homOfLE (le_unionChartSet_right a b))).hom.toRingHom))
              (Spec.map (CommRingCat.ofHom (D.map (homOfLE hra)).hom.toRingHom))
              (Spec.map (CommRingCat.ofHom (D.map (homOfLE hrb)).hom.toRingHom)),
            Nonempty ((affineIntersectionGlueData D hp).glued ⟶ Spec (.of S)) := by
  obtain ⟨n, m, P, S, hS, hsS, hP, ψ, hid, hcomp, hrec, hopen, hp⟩ :=
    exists_finite_intersection_integer_model U p hU s hs
  let := hP
  let D := algebraDiagramOfHoms (fun a ↦ (P a).ModelOfHasCoeffs S) ψ hid hcomp
  let hopen' : ∀ a b (f : a ⟶ b),
      IsOpenImmersion (Spec.map (CommRingCat.ofHom (D.map f).hom.toRingHom)) := hopen
  have hp' : ∀ (r a b : NonemptyChartSet ι) (hra : r ≤ a) (hrb : r ≤ b),
      IsPullback
        (Spec.map (CommRingCat.ofHom
          (D.map (homOfLE (le_unionChartSet_left a b))).hom.toRingHom))
        (Spec.map (CommRingCat.ofHom
          (D.map (homOfLE (le_unionChartSet_right a b))).hom.toRingHom))
        (Spec.map (CommRingCat.ofHom (D.map (homOfLE hra)).hom.toRingHom))
        (Spec.map (CommRingCat.ofHom (D.map (homOfLE hrb)).hom.toRingHom)) :=
    fun r a b hra hrb ↦ hp ⟨⟨r, a, b⟩, hra, hrb⟩
  refine ⟨S, hS, hsS, D, fun a ↦ (P a).tensorModelOfHasCoeffsEquiv S,
    ?_, hopen', hp', ⟨affineIntersectionGluedToBase D hp'⟩⟩
  intro a b f
  exact integerModelScalarExtension_recovery_hom (P a) (P b) (ψ f)
    ((finiteIntersectionSectionDiagram U p).map f).hom (hrec f)

end FLT.Mazur.Approximation
