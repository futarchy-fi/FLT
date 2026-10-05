/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteIntersectionScalarColimitRecovery
public import FLT.Mazur.FiniteIntersectionSectionComparison
public import FLT.Mazur.OpenChartSectionPullback

/-!
# Recovering ambient sections on the original intersections

The inverse colimit recovery pulls scalar-extended coordinates to the
original ambient sections, as prescribed by the tensor-coordinate equivalences.
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
  {X : Scheme.{u}} {ι : Type v} [Finite ι] (U : ι → X.Opens)
  (p : X ⟶ Spec (.of A)) [X.IsSeparated] (hU : ∀ i, IsAffineOpen (U i))
  (hcover : iSup U = ⊤) (D : NonemptyChartSet ι ⥤ CommAlgCat S)
  (e : ∀ a, A ⊗[S] D.obj a ≃ₐ[A] (finiteIntersectionSectionDiagram U p).obj a)
  (he : ∀ {a b} (f : a ⟶ b), (e b).toAlgHom.comp
    (affineScalarExtensionHom (S := A) (D.map f).hom) =
    ((finiteIntersectionSectionDiagram U p).map f).hom.comp (e a).toAlgHom)

omit [Finite ι] in
/-- Pullback through the chart recovery is its given coordinate equivalence. -/
theorem finiteIntersectionScalarRecoveryDiagramIso_inv_appTop (s : NonemptyChartSet ι) :
    (Scheme.ΓSpecIso (.of (A ⊗[S] D.obj s))).inv ≫
        ((finiteIntersectionScalarRecoveryDiagramIso U p hU D e he).inv.app (.op s)).appTop =
      CommRingCat.ofHom (e s).toRingEquiv.toRingHom := by
  change (Scheme.ΓSpecIso _).inv ≫
    ((finiteIntersectionOpen U s).toScheme.toSpecΓ ≫ Spec.map _).appTop = _
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality,
    Category.assoc, Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]
  rfl

variable
  [∀ a b (f : a ⟶ b),
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (D.map f).hom.toRingHom))]
  [((affineIntersectionSchemeDiagram (affineIntersectionScalarExtension (A := A) D)) ⋙
    Scheme.forget).IsLocallyDirected]

/-- The ambient chart pullback is the specified coordinate recovery, as a ring map. -/
theorem finiteIntersectionScalarColimitIso_sectionIso (s : NonemptyChartSet ι) :
    (affineIntersectionColimitSectionIso (affineIntersectionScalarExtension (A := A) D) s).hom ≫
        (finiteIntersectionScalarColimitIso U p hU hcover D e he).inv.appLE
          (intersectionColimitOpen
            (affineIntersectionSchemeDiagram (affineIntersectionScalarExtension (A := A) D)) s)
          (finiteIntersectionOpen U s)
          (le_of_eq (finiteIntersectionScalarColimitIso_inv_preimage U p hU hcover D e he s).symm) =
      CommRingCat.ofHom (e s).toRingEquiv.toRingHom ≫ (finiteIntersectionOpen U s).topIso.hom := by
  dsimp only [affineIntersectionColimitSectionIso, Iso.trans_hom, Iso.symm_hom,
    intersectionColimitSectionIso, intersectionColimitOpen]
  rw [Category.assoc, openChartSectionIso_pullback (finiteIntersectionOpen U s) _ _
    ((finiteIntersectionScalarRecoveryDiagramIso U p hU D e he).inv.app (.op s))
    (finiteIntersectionScalarColimitIso_inv_chart U p hU hcover D e he s),
    ← Category.assoc]
  exact congrArg (fun f ↦ f ≫ (finiteIntersectionOpen U s).topIso.hom)
    (finiteIntersectionScalarRecoveryDiagramIso_inv_appTop U p hU D e he s)

/-- On coordinates, inverse recovery gives exactly the original ambient section. -/
theorem finiteIntersectionScalarColimitIso_sectionEquiv (s : NonemptyChartSet ι)
    (x : A ⊗[S] D.obj s) :
    (finiteIntersectionScalarColimitIso U p hU hcover D e he).inv.appLE
        (intersectionColimitOpen
          (affineIntersectionSchemeDiagram (affineIntersectionScalarExtension (A := A) D)) s)
        (finiteIntersectionOpen U s)
        (le_of_eq (finiteIntersectionScalarColimitIso_inv_preimage U p hU hcover D e he s).symm)
        (affineIntersectionColimitSectionEquiv (affineIntersectionScalarExtension (A := A) D) s x) =
      (finiteIntersectionSectionEquiv U p s).symm (e s x) :=
  congrArg (fun f ↦ f x) (finiteIntersectionScalarColimitIso_sectionIso U p hU hcover D e he s)

/-- Coordinate recovery remains valid after restricting to any smaller original open. -/
theorem finiteIntersectionScalarColimitIso_sectionToOpen (s : NonemptyChartSet ι)
    (V : X.Opens) (hV : V ≤ finiteIntersectionOpen U s) (x : A ⊗[S] D.obj s) :
    (finiteIntersectionScalarColimitIso U p hU hcover D e he).inv.appLE
        (intersectionColimitOpen
          (affineIntersectionSchemeDiagram (affineIntersectionScalarExtension (A := A) D)) s) V
        (hV.trans (le_of_eq
          (finiteIntersectionScalarColimitIso_inv_preimage U p hU hcover D e he s).symm))
        (affineIntersectionColimitSectionEquiv (affineIntersectionScalarExtension (A := A) D) s x) =
      X.presheaf.map (homOfLE hV).op ((finiteIntersectionSectionEquiv U p s).symm (e s x)) := by
  rw [← finiteIntersectionScalarColimitIso_sectionEquiv U p hU hcover D e he s x,
    ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

end FLT.Mazur.Approximation
