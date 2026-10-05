/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineIntersectionModelSheaf
public import FLT.Mazur.AffineIntersectionProjectionSections
public import FLT.Mazur.ModuleUnitCocyclePullback

/-!
# Transition units under coefficient projection

The inverse-image model cocycle has the scalar-extended coordinate units
on every subopen of every finite intersection chart.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.FCurve.ModuleSheafUnitCocycle
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

variable {S A : Type u} [CommRing S] [CommRing A] [Algebra S A]
  {ι : Type u} (D : NonemptyChartSet ι ⥤ CommAlgCat S)
  (y : ∀ s, IntersectionPair s → (D.obj s)ˣ)
  (hnat : ∀ {s t} (f : s ⟶ t) (k : IntersectionPair s),
    (D.map f).hom (y s k) = (y t (intersectionPairMap f k) : D.obj t))
  (hmul : ∀ s (k : IntersectionTriple s),
    y s (k.1, k.2.1) * y s (k.2.1, k.2.2) = y s (k.1, k.2.2))

/-- Extend each transition unit along the coefficient inclusion. -/
def scalarIntersectionUnit (s : NonemptyChartSet ι) (k : IntersectionPair s) :
    ((affineIntersectionScalarExtension (A := A) D).obj s)ˣ :=
  Units.map (Algebra.TensorProduct.includeRight :
    D.obj s →ₐ[S] A ⊗[S] D.obj s).toMonoidHom (y s k)

include hnat in
/-- The scalar-extended units respect all coordinate restrictions. -/
theorem scalarIntersectionUnit_naturality {s t : NonemptyChartSet ι}
    (f : s ⟶ t) (k : IntersectionPair s) :
    ((affineIntersectionScalarExtension (A := A) D).map f).hom
        (scalarIntersectionUnit (A := A) D y s k) =
      (scalarIntersectionUnit (A := A) D y t (intersectionPairMap f k) :
        (affineIntersectionScalarExtension (A := A) D).obj t) := by
  change affineScalarExtensionHom (S := A) (D.map f).hom (1 ⊗ₜ[S] (y s k : D.obj s)) = _
  simp only [affineScalarExtensionHom, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hnat]
  rfl

include hmul in
/-- Scalar extension preserves the triple transition equations. -/
theorem scalarIntersectionUnit_mul (s : NonemptyChartSet ι) (k : IntersectionTriple s) :
    scalarIntersectionUnit (A := A) D y s (k.1, k.2.1) *
        scalarIntersectionUnit (A := A) D y s (k.2.1, k.2.2) =
      scalarIntersectionUnit (A := A) D y s (k.1, k.2.2) := by
  let m := Units.map (Algebra.TensorProduct.includeRight :
    D.obj s →ₐ[S] A ⊗[S] D.obj s).toMonoidHom
  exact (m.map_mul _ _).symm.trans (congrArg m (hmul s k))

variable [Finite ι]
  [∀ a b (f : a ⟶ b),
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (D.map f).hom.toRingHom))]
  [((affineIntersectionSchemeDiagram D) ⋙ Scheme.forget).IsLocallyDirected]
  [((affineIntersectionSchemeDiagram (affineIntersectionScalarExtension (A := A) D)) ⋙
    Scheme.forget).IsLocallyDirected]

/-- The inverse-image transition is the tensor-extended coordinate on any smaller open. -/
theorem affineIntersectionProjection_inverseImageUnit (i j : ι)
    (V : (colimit (affineIntersectionSchemeDiagram
      (affineIntersectionScalarExtension (A := A) D))).Opens)
    (hi : V ≤ colimMap (affineIntersectionProjection (A := A) D) ⁻¹ᵁ
      intersectionColimitOpen (affineIntersectionSchemeDiagram D) (singletonChartSet i))
    (hj : V ≤ colimMap (affineIntersectionProjection (A := A) D) ⁻¹ᵁ
      intersectionColimitOpen (affineIntersectionSchemeDiagram D) (singletonChartSet j))
    (s : NonemptyChartSet ι) (his : i ∈ s.val) (hjs : j ∈ s.val)
    (hV : V ≤ intersectionColimitOpen
      (affineIntersectionSchemeDiagram (affineIntersectionScalarExtension (A := A) D)) s) :
    ((affineIntersectionModelCocycle D y hnat hmul).inverseImage
        (colimMap (affineIntersectionProjection (A := A) D))).unit i j V hi hj =
      Units.map (affineIntersectionSectionToOpen (affineIntersectionScalarExtension (A := A) D)
        s V hV).toMonoidHom (scalarIntersectionUnit (A := A) D y s (⟨i, his⟩, ⟨j, hjs⟩)) := by
  apply Units.ext
  rw [Cocycle.inverseImage, Cocycle.inverseImageUnit_eq _ _ i j V hi hj
    (intersectionColimitOpen (affineIntersectionSchemeDiagram D) s)
    (intersectionColimitOpen_le_singleton _ s i his)
    (intersectionColimitOpen_le_singleton _ s j hjs)
    (hV.trans (le_of_eq (affineIntersectionProjection_preimage D s).symm))]
  rw [affineIntersectionModelCocycle_unit_eq D y hnat hmul i j _ _ _ s his hjs le_rfl]
  change (colimMap (affineIntersectionProjection (A := A) D)).appLE _ _ _
    (res le_rfl (affineIntersectionColimitSectionEquiv D s _)) = _
  rw [res_self]
  exact affineIntersectionProjection_sectionToOpen D s V hV _

end FLT.Mazur.Approximation
