/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableTranslatedHilbertOverlap
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Representability of Hilbert charts with varying translation bases

The computed intersection represents the full presheaf pullback on every
original test. If the translation base is smooth over the fixed base, the
chart map is representable by smooth morphisms. Coverage is a separate issue.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel FCurve SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] (d : ℕ) {B : X.Modules} (hB : AmpleLineBundle B)
  (T : Over (Spec (.of R))) (c : (relativeFppfSheaf f).obj.obj (op T))

/-- The actual variable-base chart map to the original Picard presheaf. -/
def variableHilbertPicardMap :
    uliftYoneda.{1}.obj (variableHilbertTest f d T) ⟶
      (relativeFppfSheaf f).obj ⋙ forget CommGrpCat where
  app U := ↾fun k ↦ variableHilbertPoint f d hB T c U.unop k.down
  naturality {U V} g := by
    apply ConcreteCategory.hom_ext
    intro k
    exact variableHilbertPoint_natural f d hB T c g.unop k.down

variable (U : Over (Spec (.of R))) (s : (relativeFppfSheaf f).obj.obj (op U))

/-- The actual intersection is the full presheaf fiber product, on arbitrary tests. -/
theorem variableHilbertPicardMap_isPullback :
    IsPullback (uliftYoneda.{1}.map (variableHilbertOverlapToChart f d hB T c U s))
      (uliftYoneda.{1}.map (variableHilbertOverlapToTest f d T c U s))
      (variableHilbertPicardMap f d hB T c) (uliftYonedaEquiv.symm s) := by
  apply IsPullback.of_forall_isPullback_app
  intro V
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro q
    change variableHilbertPoint f d hB T c V.unop
      (q.down ≫ variableHilbertOverlapToChart f d hB T c U s) =
        (relativeFppfSheaf f).obj.map (q.down ≫ variableHilbertOverlapToTest f d T c U s).op s
    rw [variableHilbertPoint_natural, variableHilbertOverlap_class]
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  · intro q r hqr
    apply ULift.ext
    exact variableHilbertOverlap_hom_ext f d hB T c U s
      (congrArg ULift.down hqr.2) (congrArg ULift.down hqr.1)
  · intro k b hkb
    obtain ⟨q, hq, _⟩ := variableHilbertOverlap_lift f d hB T c U s b.down k.down hkb
    exact ⟨ULift.up q, ULift.ext hq.2, ULift.ext hq.1⟩

/-- A smooth translation base gives smooth actual pullbacks of the chart map. -/
instance variableHilbertOverlapToTest_smooth [Smooth T.hom] :
    Smooth (variableHilbertOverlapToTest f d T c U s).left := by
  let _ : Smooth (prod.fst : prod U T ⟶ U).left := by
    rw [← Over.prodLeftIsoPullback_hom_fst U T]
    infer_instance
  change Smooth ((variableHilbertOverlapArrow f d T c U s).left ≫
    (prod.fst : prod U T ⟶ U).left)
  infer_instance

/-- An open translation base gives open actual pullbacks of the chart map. -/
instance variableHilbertOverlapToTest_isOpenImmersion [IsOpenImmersion T.hom] :
    IsOpenImmersion (variableHilbertOverlapToTest f d T c U s).left := by
  let _ : IsOpenImmersion (prod.fst : prod U T ⟶ U).left := by
    rw [← Over.prodLeftIsoPullback_hom_fst U T]
    infer_instance
  change IsOpenImmersion ((variableHilbertOverlapArrow f d T c U s).left ≫
    (prod.fst : prod U T ⟶ U).left)
  infer_instance

end FLT.Mazur.HilbertChart
