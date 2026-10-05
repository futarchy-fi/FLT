/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineIntersectionGluingSections
public import FLT.Mazur.OpenImageSectionPullback

/-!
# Ambient sections under the coefficient projection

The inverse image of each model chart is its scalar extension chart.
On these charts, pullback of an ambient coordinate is the tensor inclusion.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u v

variable {S A : Type u} [CommRing S] [CommRing A] [Algebra S A]
  {ι : Type v} [Finite ι] (D : NonemptyChartSet ι ⥤ CommAlgCat S)
  [∀ a b (f : a ⟶ b),
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (D.map f).hom.toRingHom))]
  [((affineIntersectionSchemeDiagram D) ⋙ Scheme.forget).IsLocallyDirected]
  [((affineIntersectionSchemeDiagram (affineIntersectionScalarExtension (A := A) D)) ⋙
    Scheme.forget).IsLocallyDirected]

/-- Coefficient projection has the expected chart inverse images. -/
@[simp] theorem affineIntersectionProjection_preimage (s : NonemptyChartSet ι) :
    colimMap (affineIntersectionProjection (A := A) D) ⁻¹ᵁ
        intersectionColimitOpen (affineIntersectionSchemeDiagram D) s =
      intersectionColimitOpen
        (affineIntersectionSchemeDiagram (affineIntersectionScalarExtension (A := A) D)) s :=
  TopologicalSpace.Opens.ext
    (equifibered_colimit_preimage _ (affineIntersectionProjection_equifibered D) (.op s))

/-- Ambient coordinate pullback is the tensor inclusion on coordinate rings. -/
theorem affineIntersectionProjection_sectionIso (s : NonemptyChartSet ι) :
    (affineIntersectionColimitSectionIso D s).hom ≫
        (colimMap (affineIntersectionProjection (A := A) D)).appLE
          (intersectionColimitOpen (affineIntersectionSchemeDiagram D) s)
          (intersectionColimitOpen
            (affineIntersectionSchemeDiagram (affineIntersectionScalarExtension (A := A) D)) s)
          (le_of_eq (affineIntersectionProjection_preimage D s).symm) =
      CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : D.obj s →ₐ[S] A ⊗[S] D.obj s).toRingHom ≫
        (affineIntersectionColimitSectionIso
          (affineIntersectionScalarExtension (A := A) D) s).hom := by
  dsimp only [affineIntersectionColimitSectionIso, Iso.trans_hom, Iso.symm_hom,
    intersectionColimitSectionIso, intersectionColimitOpen]
  rw [Category.assoc, openImageSectionIso_pullback _ _ _
    ((affineIntersectionProjection (A := A) D).app (.op s)) (ι_colimMap _ _)]
  change (Scheme.ΓSpecIso _).inv ≫ (Spec.map _).appTop ≫ _ = _
  rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  rfl

/-- Elementwise coordinate recovery along the coefficient projection. -/
theorem affineIntersectionProjection_sectionEquiv (s : NonemptyChartSet ι) (x : D.obj s) :
    (colimMap (affineIntersectionProjection (A := A) D)).appLE
        (intersectionColimitOpen (affineIntersectionSchemeDiagram D) s)
        (intersectionColimitOpen
          (affineIntersectionSchemeDiagram (affineIntersectionScalarExtension (A := A) D)) s)
        (le_of_eq (affineIntersectionProjection_preimage D s).symm)
        (affineIntersectionColimitSectionEquiv D s x) =
      affineIntersectionColimitSectionEquiv (affineIntersectionScalarExtension (A := A) D)
        s (1 ⊗ₜ[S] x) :=
  congrArg (fun f ↦ f x) (affineIntersectionProjection_sectionIso (A := A) D s)

/-- The coordinate comparison remains valid on every subopen of a source chart. -/
theorem affineIntersectionProjection_sectionToOpen (s : NonemptyChartSet ι)
    (V : (colimit (affineIntersectionSchemeDiagram
      (affineIntersectionScalarExtension (A := A) D))).Opens)
    (hV : V ≤ intersectionColimitOpen
      (affineIntersectionSchemeDiagram (affineIntersectionScalarExtension (A := A) D)) s)
    (x : D.obj s) :
    (colimMap (affineIntersectionProjection (A := A) D)).appLE
        (intersectionColimitOpen (affineIntersectionSchemeDiagram D) s) V
        (hV.trans (le_of_eq (affineIntersectionProjection_preimage D s).symm))
        (affineIntersectionColimitSectionEquiv D s x) =
      affineIntersectionSectionToOpen (affineIntersectionScalarExtension (A := A) D)
        s V hV (1 ⊗ₜ[S] x) := by
  change _ = (colimit (affineIntersectionSchemeDiagram
    (affineIntersectionScalarExtension (A := A) D))).presheaf.map (homOfLE hV).op
      (affineIntersectionColimitSectionEquiv (affineIntersectionScalarExtension (A := A) D)
        s (1 ⊗ₜ[S] x))
  rw [← affineIntersectionProjection_sectionEquiv D s x,
    ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

end FLT.Mazur.Approximation
