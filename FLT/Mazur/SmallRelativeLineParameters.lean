/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmallSchemePicard
public import FLT.Mazur.SmallAffineParameterBases
public import FLT.Mazur.RelativePicardFppfSheaf

/-!
# Small relative line parameters retaining the original class

Choose a small representative of each finitely presented affine base, then
encode a transported line by its actual unit cocycle. Restriction of the
chosen model class along the original base isomorphism recovers the input.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.Approximation
open FCurve SchemePicard
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- One small index for all translation lines on the chosen affine parameter bases. -/
def RelativeLineParameter : Type u :=
  Σ i : AffinePresentationIndex S, LineCocycleCode (pullback f (affinePresentationTest S i).hom)

/-- The original base test of a small line parameter. -/
def relativeLineParameterTest (p : RelativeLineParameter f) : Over S :=
  affinePresentationTest S p.1

/-- The actual line sheaf of a small parameter, obtained by cocycle gluing. -/
def relativeLineParameterLine (p : RelativeLineParameter f) :
    LineBundle (pullback f (relativeLineParameterTest f p).hom) :=
  lineOfCocycleCode _ p.2

/-- The original Picard-sheaf class of the chosen line. -/
def relativeLineParameterClass (p : RelativeLineParameter f) :
    (relativeFppfSheaf f).obj.obj (op (relativeLineParameterTest f p)) :=
  relativeFppfClass f _ (relativeClass _
    (mk (relativeLineParameterLine f p).val (relativeLineParameterLine f p).property))

/-- Every finitely presented affine-base line occurs in the fixed small parameter family. -/
theorem exists_relativeLineParameter (V : Over S)
    [IsAffine V.left] [LocallyOfFinitePresentation V.hom]
    (M : LineBundle (pullback f V.hom)) :
    ∃ (p : RelativeLineParameter f) (e : V ≅ relativeLineParameterTest f p),
      (relativeFppfSheaf f).obj.map e.hom.op (relativeLineParameterClass f p) =
        relativeFppfClass f V (relativeClass _ (mk M.val M.property)) := by
  obtain ⟨i, ⟨e⟩⟩ := exists_affinePresentationTest_iso V
  let N := (Scheme.Modules.pullback (relativeTotalMap f e.inv)).obj M.val
  have hN := M.property.pullback (relativeTotalMap f e.inv)
  obtain ⟨c, ⟨ec⟩⟩ := exists_line_cocycle_code _ ⟨N, hN⟩
  refine ⟨⟨i, c⟩, e, ?_⟩
  have hc : relativeLineParameterClass f ⟨i, c⟩ =
      (relativeFppfSheaf f).obj.map e.inv.op
        (relativeFppfClass f V (relativeClass _ (mk M.val M.property))) := by
    rw [relativeFppfClass_naturality, relativeBaseMap_class, pullback_mk]
    exact congrArg (fun a ↦ relativeFppfClass f _ (relativeClass _ a))
      (mk_eq_of_iso _ _ ec)
  change (relativeFppfSheaf f).obj.map e.hom.op
    (relativeLineParameterClass f ⟨i, c⟩) = _
  rw [hc]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    e.hom_inv_id, op_id, (relativeFppfSheaf f).obj.map_id]
  rfl

end FLT.Mazur.Approximation
