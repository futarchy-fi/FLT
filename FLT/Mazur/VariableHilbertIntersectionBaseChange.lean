/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseOpenHilbertBaseChange

/-!
# Base change of chart intersections without an open translation base

The full intersection square is a scheme pullback for every translation base.
Its proof uses both projections; the test projection need not be a monomorphism.
This permits smooth translation bases in the original quotient coverage argument.
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
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {T U : Over (Spec (.of R))} (b : U ⟶ T) (s : (relativeFppfSheaf f).obj.obj (op T))

/-- Base change preserves the actual variable Hilbert parameter. -/
@[reassoc]
theorem variableHilbertBaseChange_chart :
    baseOpenHilbertBaseChange f hL d V c b s ≫
      variableHilbertOverlapToChart f d hL V c T s =
        variableHilbertOverlapToChart f d hL V c U
          ((relativeFppfSheaf f).obj.map b.op s) :=
  (variableHilbertOverlap_lift f d hL V c T s _ _ (by
    rw [variableHilbertOverlap_class]
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply])).choose_spec.1.2

/-- Arbitrary translation bases have the full scheme base-change property. -/
theorem variableHilbertBaseChange_isPullback :
    IsPullback (baseOpenHilbertBaseChange f hL d V c b s)
      (variableHilbertOverlapToTest f d V c U ((relativeFppfSheaf f).obj.map b.op s))
      (variableHilbertOverlapToTest f d V c T s) b := by
  let lift (z : PullbackCone (variableHilbertOverlapToTest f d V c T s) b) :=
    variableHilbertOverlap_lift f d hL V c U ((relativeFppfSheaf f).obj.map b.op s)
      z.snd (z.fst ≫ variableHilbertOverlapToChart f d hL V c T s) (by
        rw [variableHilbertPoint_natural, variableHilbertOverlap_class,
          ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, z.condition]
        simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply])
  have hl z : (lift z).choose ≫ baseOpenHilbertBaseChange f hL d V c b s = z.fst := by
    apply variableHilbertOverlap_hom_ext f d hL V c T s
    · rw [Category.assoc, baseOpenHilbertBaseChange_arrow, ← Category.assoc,
        (lift z).choose_spec.1.1, z.condition]
    · rw [Category.assoc, variableHilbertBaseChange_chart, (lift z).choose_spec.1.2]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (baseOpenHilbertBaseChange_arrow f hL d V c b s) (fun z ↦ (lift z).choose)
    hl (fun z ↦ (lift z).choose_spec.1.1) ?_)
  intro z q hq ht
  apply variableHilbertOverlap_hom_ext f d hL V c U _
  · exact ht.trans (lift z).choose_spec.1.1.symm
  · apply Eq.trans _ (lift z).choose_spec.1.2.symm
    rw [← variableHilbertBaseChange_chart f hL d V c b s, ← Category.assoc, hq]

include hL in
/-- The set-theoretic image commutes with base change even without injectivity. -/
theorem variableHilbertBaseChange_range :
    b.left ⁻¹' Set.range (variableHilbertOverlapToTest f d V c T s).left =
      Set.range (variableHilbertOverlapToTest f d V c U
        ((relativeFppfSheaf f).obj.map b.op s)).left := by
  have H := (variableHilbertBaseChange_isPullback f hL d V c b s).map (Over.forget _)
  ext x
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨z, _, hz⟩ := Scheme.exists_preimage_of_isPullback H y x hy
    exact ⟨z, hz⟩
  · rintro ⟨z, rfl⟩
    exact ⟨(baseOpenHilbertBaseChange f hL d V c b s).left z,
      congrArg (fun k ↦ k.left z) (baseOpenHilbertBaseChange_arrow f hL d V c b s)⟩

end FLT.Mazur.HilbertChart
