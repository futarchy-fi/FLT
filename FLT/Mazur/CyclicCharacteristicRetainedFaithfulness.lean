/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAuxiliaryFaithfulness
public import FLT.Mazur.CompatibleSubgroupAuxiliaryTransport
public import FLT.Mazur.PulledSectionDistinctness

/-!
# Faithfulness of the retained original frames on all tests

An original frame retained by a full normalized-chart comparison stays
injective after every nonempty base change. This strengthens injectivity of
global sections to the condition required by the faithful marking open.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup GroupSectionBaseChange
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {E : GeneralizedEllipticCurve S} {n : ℕ} [NeZero n]
  (H : E.FiniteSubgroup n) (b : Bool) (q : S ⟶ normalizedLocus n b)
  (a : CompatibleIso ((normalizedSubgroup n b).baseChange q) H)
  (m : Labels (normalizedAuxiliaryOrder b) → (𝟙_ (Over S) ⟶ E.group))
  (hm : ∀ i, pullSection q (normalizedAuxiliaryMarking n b i) ≫ a.curve.hom.group = m i)

include hm in
/-- The retained original auxiliary labels remain distinct on every nonempty test. -/
theorem retainedAuxiliary_pull_injective {T : Scheme} [Nonempty T] (g : T ⟶ S) :
    Function.Injective (fun i ↦ pullSection g (m i)) := by
  let c := (compatibleBaseChangeComp (normalizedSubgroup n b) q g).trans (a.baseChange g)
  have hc (i) : pullSection (g ≫ q) (normalizedAuxiliaryMarking n b i) ≫
      c.curve.hom.group = pullSection g (m i) :=
    CompatibleIso.group_section_trans
      (compatibleBaseChangeComp (normalizedSubgroup n b) q g) (a.baseChange g)
      _ _ _ (compatibleBaseChangeComp_group_section (normalizedSubgroup n b) q g _)
      (a.baseChange_group_section g _ _ (hm i))
  intro i j hij
  apply normalizedAuxiliaryMarking_pull_injective n b (g ≫ q)
  let _ : IsIso c.curve.hom.group := inferInstanceAs (IsIso (forgetGroup.map c.curve.hom))
  exact (cancel_mono c.curve.hom.group).mp ((hc i).trans (hij.trans (hc j).symm))

include hm in
/-- The original frame satisfies the universal relative-point distinctness predicate. -/
theorem retainedAuxiliary_distinct :
    UniversallyDistinctSections.UniversallyDistinct m := by
  apply UniversallyDistinctSections.universallyDistinct_of_pull_injective
  intro T g hT
  let _ := hT
  exact retainedAuxiliary_pull_injective H b q a m hm g

end FLT.Mazur.CyclicCharacteristicAtlas
