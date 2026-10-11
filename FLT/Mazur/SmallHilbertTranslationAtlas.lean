/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePresentationHilbertTranslationCover
public import FLT.Mazur.SmallRelativeLineParameters

/-!
# One small family of charts covering the original Picard sheaf

The indices, bases and translation lines are chosen once, independently of
the test and its section. Every original section locally lifts into this
fixed family. Its parameter bases are finitely presented; smoothness of a
sufficient subfamily remains a separate geometric requirement.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel FCurve SchemePicard Approximation
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {B : X.Modules} (hB : AmpleLineBundle B)

/-- A fixed small type indexing the original variable-base translated Hilbert charts. -/
def SmallHilbertTranslationIndex : Type := RelativeLineParameter f × ℕ

/-- The actual chart belonging to one small index. -/
def smallHilbertTranslationTest (i : SmallHilbertTranslationIndex f) : Over (Spec (.of R)) :=
  variableHilbertTest f i.2 (relativeLineParameterTest f i.1)

/-- The original Picard class of a point in a chosen small chart. -/
def smallHilbertTranslationPoint (i : SmallHilbertTranslationIndex f)
    (T : Over (Spec (.of R))) (k : T ⟶ smallHilbertTranslationTest f i) :
    (relativeFppfSheaf f).obj.obj (op T) :=
  variableHilbertPoint f i.2 hB (relativeLineParameterTest f i.1)
    (relativeLineParameterClass f i.1) T k

/-- Small-chart points restrict along arbitrary original test morphisms. -/
theorem smallHilbertTranslationPoint_natural (i : SmallHilbertTranslationIndex f)
    {T U : Over (Spec (.of R))} (a : U ⟶ T) (k : T ⟶ smallHilbertTranslationTest f i) :
    smallHilbertTranslationPoint f hB i U (a ≫ k) =
      (relativeFppfSheaf f).obj.map a.op (smallHilbertTranslationPoint f hB i T k) :=
  variableHilbertPoint_natural f i.2 hB _ _ a k

include hB in
/-- The fixed small chart family covers every section on every original test. -/
theorem exists_small_hilbert_translation_cover (T : Over (Spec (.of R)))
    (s : (relativeFppfSheaf f).obj.obj (op T)) :
    ∃ C : Scheme.Cover.{0} Scheme.fppfPrecoverage T.left,
      (∀ j, IsAffine (C.X j)) ∧ ∀ j,
      ∃ (i : SmallHilbertTranslationIndex f)
        (k : relativeCoverMember T C j ⟶ smallHilbertTranslationTest f i),
        smallHilbertTranslationPoint f hB i _ k =
          (relativeFppfSheaf f).obj.map (relativeCoverArrow T C j).op s := by
  obtain ⟨C, hA, hC⟩ := exists_finitePresentation_hilbert_translation_cover f hB T s
  refine ⟨C, hA, fun j ↦ ?_⟩
  obtain ⟨V, b, M, d, k, hV, _, hu, hb, hk⟩ := hC j
  let _ := hV
  let _ := hu
  obtain ⟨p, e, he⟩ := exists_relativeLineParameter f V M
  let a := b ≫ e.hom
  let q := k ≫ variableHilbertParameter f d V
  refine ⟨⟨p, d⟩, variableHilbertLift f d _ a q, ?_⟩
  change variableHilbertPoint f d hB _ _ _ (variableHilbertLift f d _ a q) = _
  rw [variableHilbertPoint_lift]
  have ha : (relativeFppfSheaf f).obj.map a.op (relativeLineParameterClass f p) =
      (relativeFppfSheaf f).obj.map b.op
        (relativeFppfClass f V (relativeClass _ (mk M.val M.property))) := by
    rw [show a = b ≫ e.hom from rfl, op_comp, Functor.map_comp,
      ConcreteCategory.comp_apply, he]
  rw [ha]
  simpa only [variableHilbertPoint, hb] using hk

end FLT.Mazur.HilbertChart
