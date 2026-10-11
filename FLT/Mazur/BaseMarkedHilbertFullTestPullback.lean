/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseMarkedHilbertFullTestChange

/-!
# Full original test changes are actual scheme pullbacks

The complete relative universal property gives the scheme pullback square,
so geometric properties of the original test map transfer to the comparison.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {X : Scheme} (f : X ⟶ Spec (.of R))
  [Algebra.FiniteType ℤ R] [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (V : Over (Spec (.of R))) {ι : Type} (a : ι → BaseMarkedHilbertIndex f V)
  {U W : Over (Spec (.of R))} (b : W ⟶ U)
  (s : (relativeFppfSheaf f).obj.obj (op U))
local notation "sW" => CategoryTheory.Functor.map
  (ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)) b.op s

/-- Changing the original test is cartesian, with both original projections. -/
theorem baseMarkedFullTestChange_isPullback :
    IsPullback (baseMarkedFullTestChange f hL V a b s) (baseMarkedFullToTest f V a W sW)
      (baseMarkedFullToTest f V a U s) b := by
  have hc (z : PullbackCone (baseMarkedFullToTest f V a U s) b) :
      baseMarkedGluedPoint f hL V a z.pt (z.fst ≫ baseMarkedFullToGlued f hL V a U s) =
        (relativeFppfSheaf f).obj.map z.snd.op sW := by
    rw [baseMarkedGluedPoint_natural, baseMarkedFullToGlued_class]
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, z.condition]
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  let l (z : PullbackCone (baseMarkedFullToTest f V a U s) b) :=
    baseMarkedFullLift f hL V a W sW z.snd (z.fst ≫ baseMarkedFullToGlued f hL V a U s) (hc z)
  have ht z : l z ≫ baseMarkedFullToTest f V a W sW = z.snd :=
    baseMarkedFullLift_toTest f hL V a W sW _ _ _
  have hg z : l z ≫ baseMarkedFullToGlued f hL V a W sW =
      z.fst ≫ baseMarkedFullToGlued f hL V a U s :=
    baseMarkedFullLift_toGlued f hL V a W sW _ _ _
  have hl z : l z ≫ baseMarkedFullTestChange f hL V a b s = z.fst := by
    apply baseMarkedFull_hom_ext f hL V a U s
    · rw [Category.assoc, baseMarkedFullTestChange_test, ← Category.assoc, ht]
      exact z.condition.symm
    · rw [Category.assoc, baseMarkedFullTestChange_glued, hg]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (baseMarkedFullTestChange_test f hL V a b s) l hl ht ?_)
  intro z q hq hqt
  apply baseMarkedFull_hom_ext f hL V a W sW
  · exact hqt.trans (ht z).symm
  · rw [hg, ← baseMarkedFullTestChange_glued f hL V a b s, ← Category.assoc, hq]

/-- Any base-change-stable property of the original test map holds for the full comparison. -/
theorem baseMarkedFullTestChange_property (P : MorphismProperty Scheme)
    [P.IsStableUnderBaseChange] (hb : P b.left) :
    P (baseMarkedFullTestChange f hL V a b s).left :=
  MorphismProperty.of_isPullback
    ((baseMarkedFullTestChange_isPullback f hL V a b s).map (Over.forget _)).flip hb

instance baseMarkedFullTestChange_isOpenImmersion [IsOpenImmersion b.left] :
    IsOpenImmersion (baseMarkedFullTestChange f hL V a b s).left :=
  baseMarkedFullTestChange_property f hL V a b s _ inferInstance

end FLT.Mazur.HilbertChart
