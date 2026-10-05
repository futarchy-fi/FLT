/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineIntersectionProjectionSections
public import FLT.Mazur.FiniteIntersectionScalarGluingRecovery

/-!
# Chartwise recovery of the scalar-extended colimit

Compatible tensor-coordinate identifications recover the original covered
scheme. The inverse recovery carries each original intersection exactly to
its colimit chart, with a commuting square of the actual chart morphisms.
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

/-- Recover the tensor-extended spectrum diagram as the actual intersection diagram. -/
def finiteIntersectionScalarRecoveryDiagramIso :
    affineIntersectionSchemeDiagram (affineIntersectionScalarExtension (A := A) D) ≅
      finiteIntersectionSchemeDiagram U :=
  affineIntersectionScalarExtensionSpecIso D (finiteIntersectionSectionDiagram U p) e he ≪≫
    (finiteIntersectionCoordinateDiagramIso U p hU).symm

variable
  [∀ a b (f : a ⟶ b),
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (D.map f).hom.toRingHom))]
  [((affineIntersectionSchemeDiagram (affineIntersectionScalarExtension (A := A) D)) ⋙
    Scheme.forget).IsLocallyDirected]

/-- Recovery from the chosen scalar-extended colimit to the original covered scheme. -/
def finiteIntersectionScalarColimitIso :
    colimit (affineIntersectionSchemeDiagram (affineIntersectionScalarExtension (A := A) D)) ≅
      X :=
  HasColimit.isoOfNatIso (finiteIntersectionScalarRecoveryDiagramIso U p hU D e he) ≪≫
    (colimit.isColimit (finiteIntersectionSchemeDiagram U)).coconePointUniqueUpToIso
      (finiteIntersectionSchemeCoconeIsColimit U hcover)

/-- Recovery on a chart is precisely its specified coordinate isomorphism. -/
@[reassoc]
theorem finiteIntersectionScalarColimitIso_chart (s : NonemptyChartSet ι) :
    colimit.ι (affineIntersectionSchemeDiagram
        (affineIntersectionScalarExtension (A := A) D)) (.op s) ≫
        (finiteIntersectionScalarColimitIso U p hU hcover D e he).hom =
      (finiteIntersectionScalarRecoveryDiagramIso U p hU D e he).hom.app (.op s) ≫
        (finiteIntersectionOpen U s).ι := by
  simp only [finiteIntersectionScalarColimitIso, Iso.trans_hom,
    HasColimit.ι_isoOfNatIso_hom_assoc, colimit.comp_coconePointUniqueUpToIso_hom]
  rfl

/-- The inverse recovery square commutes on each original intersection. -/
@[reassoc]
theorem finiteIntersectionScalarColimitIso_inv_chart (s : NonemptyChartSet ι) :
    (finiteIntersectionOpen U s).ι ≫
        (finiteIntersectionScalarColimitIso U p hU hcover D e he).inv =
      (finiteIntersectionScalarRecoveryDiagramIso U p hU D e he).inv.app (.op s) ≫
        colimit.ι (affineIntersectionSchemeDiagram
          (affineIntersectionScalarExtension (A := A) D)) (.op s) := by
  rw [← cancel_mono (finiteIntersectionScalarColimitIso U p hU hcover D e he).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    finiteIntersectionScalarColimitIso_chart]
  simp

/-- Inverse recovery takes each original intersection to exactly its colimit chart. -/
@[simp] theorem finiteIntersectionScalarColimitIso_inv_preimage (s : NonemptyChartSet ι) :
    (finiteIntersectionScalarColimitIso U p hU hcover D e he).inv ⁻¹ᵁ
        intersectionColimitOpen
          (affineIntersectionSchemeDiagram (affineIntersectionScalarExtension (A := A) D)) s =
      finiteIntersectionOpen U s := by
  let E := finiteIntersectionScalarColimitIso U p hU hcover D e he
  let N := finiteIntersectionScalarRecoveryDiagramIso U p hU D e he
  apply TopologicalSpace.Opens.ext
  ext x
  constructor
  · rintro ⟨z, hz⟩
    have hc := congrArg (fun f : _ ⟶ X ↦ f z)
      (finiteIntersectionScalarColimitIso_chart U p hU hcover D e he s)
    have hx : (finiteIntersectionOpen U s).ι (N.hom.app (.op s) z) = x := by
      calc
        _ = E.hom (colimit.ι (affineIntersectionSchemeDiagram
          (affineIntersectionScalarExtension (A := A) D)) (.op s) z) := hc.symm
        _ = E.hom (E.inv x) := congrArg (fun t ↦ E.hom t) hz
        _ = x := by change (E.inv ≫ E.hom) x = x; simp
    exact hx ▸ (N.hom.app (.op s) z).property
  · intro hx
    refine ⟨N.inv.app (.op s) ⟨x, hx⟩, ?_⟩
    exact (congrArg (fun f ↦ f ⟨x, hx⟩)
      (finiteIntersectionScalarColimitIso_inv_chart U p hU hcover D e he s)).symm

end FLT.Mazur.Approximation
