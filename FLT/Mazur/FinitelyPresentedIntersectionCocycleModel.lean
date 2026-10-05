/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineIntersectionDiagramGluing
public import FLT.Mazur.FiniteIntersectionClosedModel
public import FLT.Mazur.IntegerModelClosedProductTransport
public import FLT.Mazur.FiniteIntersectionCocycleUnits
public import FLT.Mazur.FiniteDiagramUnitDescent
public import FLT.Mazur.IntegerModelPullbackTransport

/-!
# Finitely presented line cocycle models with closed overlap products

The coefficient construction retains finite presentation of every model
chart algebra, alongside closed products, transition units, and recovery.
This supplies the finiteness evidence needed by the glued model.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

/-- Descend an intersection atlas and its actual transition units at one coefficient stage. -/
theorem exists_finite_presentation_intersection_closed_cocycle_model {A : Type u} [CommRing A]
    {X : Scheme.{u}} {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (p : X ⟶ Spec (.of A)) [X.IsSeparated] [LocallyOfFinitePresentation p]
    (hU : ∀ i, IsAffineOpen (U i))
    (g : FLT.Mazur.FCurve.ModuleSheafUnitCocycle.Cocycle U) (s : Set A) (hs : s.Finite) :
    let C := finiteIntersectionSectionDiagram U p
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ s ⊆ S ∧
      ∃ D : NonemptyChartSet ι ⥤ CommAlgCat S,
        (∀ a, Algebra.FinitePresentation S (D.obj a)) ∧
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
            (∀ a b, IsClosedImmersion (Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.productMap
                (D.map (homOfLE (le_unionChartSet_left a b))).hom
                (D.map (homOfLE (le_unionChartSet_right a b))).hom).toRingHom))) ∧
            ∃ y : ∀ a, IntersectionPair a → (D.obj a)ˣ,
              (∀ a k, e a (1 ⊗ₜ (y a k : D.obj a)) =
                (finiteIntersectionCocycleUnit U p g a k : C.obj a)) ∧
              (∀ {a b} (f : a ⟶ b) k, (D.map f).hom (y a k) =
                (y b (intersectionPairMap f k) : D.obj b)) ∧
              ∀ a (k : IntersectionTriple a),
                y a (k.1, k.2.1) * y a (k.2.1, k.2.2) = y a (k.1, k.2.2) := by
  classical
  let C := finiteIntersectionSectionDiagram U p
  obtain ⟨n, m, P, R, hR, _, hPR, ψ₀, hid₀, hcomp₀, hrec₀, hopen₀, hc₀, hp₀⟩ :=
    exists_finite_intersection_closed_model U p hU ∅ Set.finite_empty
  let := hR
  let := hPR
  obtain ⟨S, hS, hsS, hRS, hP, y, hy, hnat, hmul⟩ :=
    exists_finite_diagram_unit_model (fun a ↦ ↥(C.obj a)) n m P R
      (fun f ↦ (C.map f).hom) ψ₀ hrec₀ IntersectionPair IntersectionTriple
      (finiteIntersectionCocycleUnit U p g) (fun f ↦ intersectionPairMap f)
      (finiteIntersectionCocycleUnit_naturality U p g)
      (fun _ k ↦ (k.1, k.2.1)) (fun _ k ↦ (k.2.1, k.2.2))
      (fun _ k ↦ (k.1, k.2.2)) (finiteIntersectionCocycleUnit_mul U p g) s hs
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
  have hc a b : IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.productMap
        (D.map (homOfLE (le_unionChartSet_left a b))).hom
        (D.map (homOfLE (le_unionChartSet_right a b))).hom).toRingHom)) :=
    integerModelTransportHom_product_closedImmersion (P a) (P b) (P (unionChartSet a b))
      hRS _ _ (hc₀ a b)
  have hfp : ∀ a, Algebra.FinitePresentation S (D.obj a) := fun a ↦
    inferInstanceAs (Algebra.FinitePresentation S ((P a).ModelOfHasCoeffs S))
  refine ⟨S, hS, hsS, D, hfp, fun a ↦ (P a).tensorModelOfHasCoeffsEquiv S,
    ?_, hopen', hp', hc, y, hy, hnat, hmul⟩
  intro a b f
  exact integerModelScalarExtension_recovery_hom (P a) (P b) (ψ f)
    ((finiteIntersectionSectionDiagram U p).map f).hom (hrec f)

end FLT.Mazur.Approximation
