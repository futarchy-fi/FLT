/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseMarkedHilbertGluedInjectivity

/-!
# Changing the translation base of an actual Hilbert chart

The product parameter changes with the translation base. Its original Picard
class is unchanged when the translating section is pulled back along that map.
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

/-- Pull back the actual translating section without changing the degree. -/
def baseMarkedIndexChange (i : BaseMarkedHilbertIndex f V) : BaseMarkedHilbertIndex f W :=
  (i.1, (relativeFppfSheaf f).obj.map b.op i.2)

/-- The map of actual parameter schemes induced by the translation-base map. -/
def baseMarkedChartChange (d : ℕ) : variableHilbertTest f d W ⟶ variableHilbertTest f d V :=
  variableHilbertLift f d V (variableHilbertBase f d W ≫ b)
    (variableHilbertParameter f d W)

@[reassoc]
theorem baseMarkedChartChange_base (d : ℕ) :
    baseMarkedChartChange f b d ≫ variableHilbertBase f d V =
      variableHilbertBase f d W ≫ b := prod.lift_fst _ _

@[reassoc]
theorem baseMarkedChartChange_parameter (d : ℕ) :
    baseMarkedChartChange f b d ≫ variableHilbertParameter f d V =
      variableHilbertParameter f d W := prod.lift_snd _ _

/-- Changing the base preserves the original translated class on every original test. -/
theorem baseMarkedChartChange_class (i : BaseMarkedHilbertIndex f V)
    {U : Over (Spec (.of R))} (k : U ⟶ variableHilbertTest f i.1 W) :
    variableHilbertPoint f i.1 hL V i.2 U (k ≫ baseMarkedChartChange f b i.1) =
      variableHilbertPoint f i.1 hL W (baseMarkedIndexChange f b i).2 U k := by
  simp only [variableHilbertPoint, Category.assoc, baseMarkedChartChange_base,
    baseMarkedChartChange_parameter, baseMarkedIndexChange, op_comp, Functor.map_comp,
    ConcreteCategory.comp_apply]

/-- The chart comparison is the actual pullback over the translation base. -/
theorem baseMarkedChartChange_isPullback (d : ℕ) :
    IsPullback (baseMarkedChartChange f b d) (variableHilbertBase f d W)
      (variableHilbertBase f d V) b := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (baseMarkedChartChange_base f b d)
    (fun z ↦ variableHilbertLift f d W z.snd (z.fst ≫ variableHilbertParameter f d V))
    (fun z ↦ ?_) (fun z ↦ prod.lift_fst _ _) (fun z q hq ht ↦ ?_))
  · apply prod.hom_ext
    · change _ ≫ variableHilbertBase f d V = _
      rw [Category.assoc, baseMarkedChartChange_base]
      simpa only [variableHilbertLift, variableHilbertBase, prod.lift_fst_assoc] using
        z.condition.symm
    · change _ ≫ variableHilbertParameter f d V = _
      rw [Category.assoc, baseMarkedChartChange_parameter]
      exact prod.lift_snd _ _
  · apply prod.hom_ext
    · exact ht.trans (prod.lift_fst _ _).symm
    · change q ≫ variableHilbertParameter f d W = _
      rw [← baseMarkedChartChange_parameter f b d, ← Category.assoc, hq]
      exact (prod.lift_snd _ _).symm

end FLT.Mazur.HilbertChart
