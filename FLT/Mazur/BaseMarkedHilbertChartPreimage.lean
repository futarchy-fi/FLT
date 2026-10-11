/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseMarkedHilbertChangePicard

/-!
# The preimage of an actual glued chart under translation-base change

A target chart point and a compatible source glued point recover a source
chart point. The proof retains the source base map and original Picard class.
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
  {V W : Over (Spec (.of R))} (b : W ⟶ V)
  {ι : Type} (a : ι → BaseMarkedHilbertIndex f V) (i : ι)
local notation "aW" => fun i ↦ baseMarkedIndexChange f b (a i)

/-- The changed chart represents precisely the preimage of the original glued chart. -/
theorem baseMarkedGluedChange_chart_lift {U : Over (Spec (.of R))}
    (p : U ⟶ baseMarkedGluedTest f hL W aW)
    (k : U ⟶ variableHilbertTest f (a i).1 V)
    (he : p ≫ baseMarkedGluedChange f hL b a = k ≫ baseMarkedGluedArrow f hL V a i) :
    ∃! q : U ⟶ variableHilbertTest f (a i).1 W,
      q ≫ baseMarkedGluedArrow f hL W aW i = p ∧
        q ≫ baseMarkedChartChange f b (a i).1 = k := by
  have hb : k ≫ variableHilbertBase f (a i).1 V =
      (p ≫ baseMarkedGluedBase f hL W aW) ≫ b := by
    rw [← baseMarkedGluedArrow_base f hL V a i, ← Category.assoc, ← he,
      Category.assoc, baseMarkedGluedChange_base, Category.assoc]
  let H := baseMarkedChartChange_isPullback f b (a i).1
  let q := H.lift k (p ≫ baseMarkedGluedBase f hL W aW) hb
  have hq : q ≫ baseMarkedChartChange f b (a i).1 = k := H.lift_fst _ _ _
  have hqb : q ≫ variableHilbertBase f (a i).1 W =
      p ≫ baseMarkedGluedBase f hL W aW := H.lift_snd _ _ _
  have hp : q ≫ baseMarkedGluedArrow f hL W aW i = p := by
    apply baseMarkedGluedPoint_injective_over f hL W aW
    · rw [Category.assoc, baseMarkedGluedArrow_base]
      exact hqb
    · rw [baseMarkedGluedPoint_chart]
      change variableHilbertPoint f (a i).1 hL W (aW i).2 U q = _
      rw [← baseMarkedChartChange_class f hL b (a i) q,
        hq, ← baseMarkedGluedPoint_chart f hL V a i k, ← he,
        baseMarkedGluedChange_point]
  refine ⟨q, ⟨hp, hq⟩, ?_⟩
  intro r hr
  apply H.hom_ext
  · exact hr.2.trans hq.symm
  · rw [hqb, ← hr.1, Category.assoc, baseMarkedGluedArrow_base]
    rfl

/-- The original open chart square is cartesian in the category of original relative tests. -/
theorem baseMarkedGluedChange_chart_isPullback :
    IsPullback (baseMarkedGluedArrow f hL W aW i) (baseMarkedChartChange f b (a i).1)
      (baseMarkedGluedChange f hL b a) (baseMarkedGluedArrow f hL V a i) := by
  let lift (z : PullbackCone (baseMarkedGluedChange f hL b a)
      (baseMarkedGluedArrow f hL V a i)) :=
    baseMarkedGluedChange_chart_lift f hL b a i z.fst z.snd z.condition
  exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (baseMarkedGluedChange_chart f hL b a i) (fun z ↦ (lift z).choose)
    (fun z ↦ (lift z).choose_spec.1.1) (fun z ↦ (lift z).choose_spec.1.2)
    (fun z q hq ht ↦ (lift z).choose_spec.2 q ⟨hq, ht⟩))

end FLT.Mazur.HilbertChart
