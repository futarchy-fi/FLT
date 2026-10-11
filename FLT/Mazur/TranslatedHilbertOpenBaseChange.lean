/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TranslatedHilbertPicardChart
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Exact base change of a translated Hilbert open

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
  (d : ℕ) (c : (relativeFppfSheaf f).obj.obj (op (Over.mk (𝟙 (Spec (.of R))))))
  {T U : Over (Spec (.of R))} (b : U ⟶ T) (s : (relativeFppfSheaf f).obj.obj (op T))

/-- The actual restricted chart intersection maps to the original one. -/
def translatedOpenBaseChange :
    translatedHilbertOverlapTest f d c U ((relativeFppfSheaf f).obj.map b.op s) ⟶
      translatedHilbertOverlapTest f d c T s :=
  (translatedHilbertOverlap_lift f d hL c T s
    (translatedHilbertOverlapArrow f d c U ((relativeFppfSheaf f).obj.map b.op s) ≫ b)
    (translatedHilbertOverlapToParameter f d hL c U ((relativeFppfSheaf f).obj.map b.op s))
    (by
      rw [translatedHilbertOverlap_class]
      simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply])).choose

@[reassoc]
theorem translatedOpenBaseChange_arrow :
    translatedOpenBaseChange f hL d c b s ≫ translatedHilbertOverlapArrow f d c T s =
      translatedHilbertOverlapArrow f d c U ((relativeFppfSheaf f).obj.map b.op s) ≫ b :=
  (translatedHilbertOverlap_lift f d hL c T s _ _ (by
    rw [translatedHilbertOverlap_class]
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply])).choose_spec.1.1

/-- The constructed square is a scheme pullback, not merely a square on rational points. -/
theorem translatedOpenBaseChange_isPullback :
    IsPullback (translatedOpenBaseChange f hL d c b s)
      (translatedHilbertOverlapArrow f d c U ((relativeFppfSheaf f).obj.map b.op s))
      (translatedHilbertOverlapArrow f d c T s) b := by
  let _ : Mono (translatedHilbertOverlapArrow f d c T s) := Over.mono_of_mono_left _
  let _ : Mono (translatedHilbertOverlapArrow f d c U
    ((relativeFppfSheaf f).obj.map b.op s)) := Over.mono_of_mono_left _
  let lift (z : PullbackCone (translatedHilbertOverlapArrow f d c T s) b) :=
    translatedHilbertOverlap_lift f d hL c U ((relativeFppfSheaf f).obj.map b.op s)
      z.snd (z.fst ≫ translatedHilbertOverlapToParameter f d hL c T s) (by
        rw [translatedHilbertPicardPoint_natural, translatedHilbertOverlap_class,
          ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, z.condition]
        simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply])
  have hl z : (lift z).choose ≫ translatedOpenBaseChange f hL d c b s = z.fst := by
    apply (cancel_mono (translatedHilbertOverlapArrow f d c T s)).mp
    rw [Category.assoc, translatedOpenBaseChange_arrow, ← Category.assoc,
      (lift z).choose_spec.1.1, z.condition]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (translatedOpenBaseChange_arrow f hL d c b s) (fun z ↦ (lift z).choose)
    hl (fun z ↦ (lift z).choose_spec.1.1) ?_)
  intro z q _ hq
  exact (cancel_mono (translatedHilbertOverlapArrow f d c U
    ((relativeFppfSheaf f).obj.map b.op s))).mp (hq.trans (lift z).choose_spec.1.1.symm)

include hL in
/-- The chart's open range commutes with arbitrary original base change. -/
theorem translatedOpen_preimage :
    b.left ⁻¹ᵁ (translatedHilbertOverlapArrow f d c T s).left.opensRange =
      (translatedHilbertOverlapArrow f d c U
        ((relativeFppfSheaf f).obj.map b.op s)).left.opensRange := by
  have H := (translatedOpenBaseChange_isPullback f hL d c b s).map (Over.forget _)
  ext x
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨z, _, hz⟩ := Scheme.exists_preimage_of_isPullback H y x hy
    exact ⟨z, hz⟩
  · rintro ⟨z, rfl⟩
    exact ⟨(translatedOpenBaseChange f hL d c b s).left z,
      congrArg (fun k ↦ k.left z) (translatedOpenBaseChange_arrow f hL d c b s)⟩

end FLT.Mazur.HilbertChart
