/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableTranslatedHilbertRepresentation
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Base-local translated Hilbert opens on original tests

The original chart-test intersection commutes with arbitrary test morphisms.
In particular its open range pulls back exactly, an ingredient in descending
these concrete Picard opens to the orbit quotient.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsOpenImmersion V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {T U : Over (Spec (.of R))} (b : U ⟶ T) (s : (relativeFppfSheaf f).obj.obj (op T))

/-- A base-open translation gives an injective chart map on every original test. -/
theorem baseOpenHilbertPoint_injective (U : Over (Spec (.of R))) :
    Function.Injective (variableHilbertPoint f d hL V c U) := by
  intro k l h
  apply variableHilbertPoint_injective_over f d hL V c _ h
  apply Over.OverMorphism.ext
  apply (cancel_mono V.hom).mp
  exact (Over.w _).trans (Over.w _).symm

/-- The actual restricted chart intersection maps to the original one. -/
def baseOpenHilbertBaseChange :
    variableHilbertOverlap f d V c U ((relativeFppfSheaf f).obj.map b.op s) ⟶
      variableHilbertOverlap f d V c T s :=
  (variableHilbertOverlap_lift f d hL V c T s
    (variableHilbertOverlapToTest f d V c U ((relativeFppfSheaf f).obj.map b.op s) ≫ b)
    (variableHilbertOverlapToChart f d hL V c U ((relativeFppfSheaf f).obj.map b.op s))
    (by
      rw [variableHilbertOverlap_class]
      simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply])).choose

omit [IsOpenImmersion V.hom] in
@[reassoc]
theorem baseOpenHilbertBaseChange_arrow :
    baseOpenHilbertBaseChange f hL d V c b s ≫ variableHilbertOverlapToTest f d V c T s =
      variableHilbertOverlapToTest f d V c U ((relativeFppfSheaf f).obj.map b.op s) ≫ b :=
  (variableHilbertOverlap_lift f d hL V c T s _ _ (by
    rw [variableHilbertOverlap_class]
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply])).choose_spec.1.1

/-- The constructed square is a scheme pullback, not merely a square on rational points. -/
theorem baseOpenHilbertBaseChange_isPullback :
    IsPullback (baseOpenHilbertBaseChange f hL d V c b s)
      (variableHilbertOverlapToTest f d V c U ((relativeFppfSheaf f).obj.map b.op s))
      (variableHilbertOverlapToTest f d V c T s) b := by
  let _ : Mono (variableHilbertOverlapToTest f d V c T s) := Over.mono_of_mono_left _
  let _ : Mono (variableHilbertOverlapToTest f d V c U
    ((relativeFppfSheaf f).obj.map b.op s)) := Over.mono_of_mono_left _
  let lift (z : PullbackCone (variableHilbertOverlapToTest f d V c T s) b) :=
    variableHilbertOverlap_lift f d hL V c U ((relativeFppfSheaf f).obj.map b.op s)
      z.snd (z.fst ≫ variableHilbertOverlapToChart f d hL V c T s) (by
        rw [variableHilbertPoint_natural, variableHilbertOverlap_class,
          ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, z.condition]
        simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply])
  have hl z : (lift z).choose ≫ baseOpenHilbertBaseChange f hL d V c b s = z.fst := by
    apply (cancel_mono (variableHilbertOverlapToTest f d V c T s)).mp
    rw [Category.assoc, baseOpenHilbertBaseChange_arrow, ← Category.assoc,
      (lift z).choose_spec.1.1, z.condition]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (baseOpenHilbertBaseChange_arrow f hL d V c b s) (fun z ↦ (lift z).choose)
    hl (fun z ↦ (lift z).choose_spec.1.1) ?_)
  intro z q _ hq
  exact (cancel_mono (variableHilbertOverlapToTest f d V c U
    ((relativeFppfSheaf f).obj.map b.op s))).mp (hq.trans (lift z).choose_spec.1.1.symm)

include hL in
/-- The chart's open range commutes with arbitrary original base change. -/
theorem baseOpenHilbert_preimage :
    b.left ⁻¹ᵁ (variableHilbertOverlapToTest f d V c T s).left.opensRange =
      (variableHilbertOverlapToTest f d V c U
        ((relativeFppfSheaf f).obj.map b.op s)).left.opensRange := by
  have H := (baseOpenHilbertBaseChange_isPullback f hL d V c b s).map (Over.forget _)
  ext x
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨z, _, hz⟩ := Scheme.exists_preimage_of_isPullback H y x hy
    exact ⟨z, hz⟩
  · rintro ⟨z, rfl⟩
    exact ⟨(baseOpenHilbertBaseChange f hL d V c b s).left z,
      congrArg (fun k ↦ k.left z) (baseOpenHilbertBaseChange_arrow f hL d V c b s)⟩

end FLT.Mazur.HilbertChart
