/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertChartRelationOperations
public import FLT.Mazur.RelativePicardFppfSingletonDescent
public import FLT.Mazur.RelativeFppfPairCover

/-!
# An effective full Hilbert quotient embeds into the original Picard presheaf

The original section descends uniquely to any actual fppf scheme kernel-pair
model. The descended section separates maps from every original test scheme,
proved by simultaneous fppf lifting of two maps into the quotient.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
local notation "P" => variableChartRelationFst f hL d V c
local notation "Q" => variableChartRelationSnd f hL d V c
local notation "s" => variableChartSection f hL d V c
variable {Z : Over (Spec (.of R))} (π : variableHilbertTest f d V ⟶ Z)
  (H : IsPullback (variableChartRelationFst f hL d V c)
    (variableChartRelationSnd f hL d V c) π π)
  [Flat π.left] [LocallyOfFinitePresentation π.left] [Surjective π.left]

omit [Flat π.left] [LocallyOfFinitePresentation π.left] [Surjective π.left] in
include H in
/-- The original universal class agrees on the actual quotient kernel pair. -/
theorem effectivePicardSection_kernel :
    (relativeFppfSheaf f).obj.map (pullback.fst π π).op s =
      (relativeFppfSheaf f).obj.map (pullback.snd π π).op s := by
  have hc := congrArg
    ((relativeFppfSheaf f).obj.map (H.lift (pullback.fst π π) (pullback.snd π π)
      pullback.condition).op) (variableChartRelation_class f hL d V c)
  simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    H.lift_fst, H.lift_snd] using hc

/-- The actual original Picard section on the effective scheme quotient. -/
def effectivePicardSection : (relativeFppfSheaf f).obj.obj (op Z) :=
  (relativePicardFppf_singleton_existsUnique f π s
    (effectivePicardSection_kernel f hL d V c π H)).choose

/-- Its pullback is the unchanged original variable Hilbert section. -/
theorem effectivePicardSection_source :
    (relativeFppfSheaf f).obj.map π.op (effectivePicardSection f hL d V c π H) = s :=
  (relativePicardFppf_singleton_existsUnique f π s
    (effectivePicardSection_kernel f hL d V c π H)).choose_spec.1

/-- The original source determines the descended section uniquely. -/
theorem effectivePicardSection_unique (t : (relativeFppfSheaf f).obj.obj (op Z))
    (ht : (relativeFppfSheaf f).obj.map π.op t = s) :
    t = effectivePicardSection f hL d V c π H :=
  relativePicardFppf_singleton_injective f π
    (ht.trans (effectivePicardSection_source f hL d V c π H).symm)

/-- The descended class detects maps from every original test into the effective model. -/
theorem effectivePicardSection_injective (T : Over (Spec (.of R))) :
    Function.Injective (fun a : T ⟶ Z ↦
      (relativeFppfSheaf f).obj.map a.op (effectivePicardSection f hL d V c π H)) := by
  intro a b hab
  let t := RelativeFppfPairCover.cover π a b
  let u := RelativeFppfPairCover.fst π a b
  let v := RelativeFppfPairCover.snd π a b
  have hu : u ≫ π = t ≫ a := RelativeFppfPairCover.fst_map π a b
  have hv : v ≫ π = t ≫ b := RelativeFppfPairCover.snd_map π a b
  have huv : (relativeFppfSheaf f).obj.map u.op s =
      (relativeFppfSheaf f).obj.map v.op s := by
    rw [← effectivePicardSection_source f hL d V c π H]
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hu, hv]
    simpa only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using
      congrArg ((relativeFppfSheaf f).obj.map t.op) hab
  let r := variableChartRelationLift f hL d V c u v huv
  have hr : r ≫ P = u := variableChartRelationLift_fst f hL d V c u v huv
  have hr' : r ≫ Q = v := variableChartRelationLift_snd f hL d V c u v huv
  have ht : t ≫ a = t ≫ b := by
    rw [← hu, ← hv, ← hr, ← hr', Category.assoc, Category.assoc, H.w]
  apply (Over.forget _).map_injective
  exact (cancel_epi t.left).mp (congrArg Over.Hom.left ht)

/-- The actual quotient's map into the original Picard presheaf. -/
def effectivePicardMap : uliftYoneda.{1}.obj Z ⟶
    (relativeFppfSheaf f).obj ⋙ forget CommGrpCat :=
  uliftYonedaEquiv.symm (effectivePicardSection f hL d V c π H)

/-- The model's map to Picard agrees with the original chart on its whole source. -/
@[reassoc]
theorem effectivePicardMap_source :
    uliftYoneda.{1}.map π ≫ effectivePicardMap f hL d V c π H =
      variableHilbertPicardMap f d hL V c := by
  ext T a
  change (relativeFppfSheaf f).obj.map (a.down ≫ π).op
    (effectivePicardSection f hL d V c π H) = _
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
    effectivePicardSection_source]
  exact variableChartSection_map f hL d V c a.down

/-- The model represents a subfunctor of the original Picard functor, on all tests. -/
instance effectivePicardMap_mono : Mono (effectivePicardMap f hL d V c π H) := by
  suffices ∀ T, Mono ((effectivePicardMap f hL d V c π H).app T) from
    NatTrans.mono_of_mono_app _
  intro T
  rw [CategoryTheory.mono_iff_injective]
  intro a b hab
  apply ULift.ext
  exact effectivePicardSection_injective f hL d V c π H T.unop hab

end FLT.Mazur.HilbertChart
