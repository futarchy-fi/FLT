/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TranslatedHilbertPicardChart

/-!
# Hilbert charts translated by sections on a varying base

A translation on an original test T defines a genuine parameter scheme:
the fiber product of T with the acyclic Hilbert scheme. The resulting
Picard map retains both the parameter-base map and the Hilbert map.
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
  (T : Over (Spec (.of R)))

/-- The actual parameter scheme for a translation living over T. -/
def variableHilbertTest : Over (Spec (.of R)) := prod T (acyclicHilbertTest f d)

/-- The remembered map to the base on which the translation is defined. -/
def variableHilbertBase : variableHilbertTest f d T ⟶ T := prod.fst

/-- The remembered map to the original Hilbert parameter scheme. -/
def variableHilbertParameter : variableHilbertTest f d T ⟶ acyclicHilbertTest f d := prod.snd

/-- Independent compatible parameter and base maps give a point of the actual chart. -/
def variableHilbertLift {U : Over (Spec (.of R))}
    (b : U ⟶ T) (k : U ⟶ acyclicHilbertTest f d) : U ⟶ variableHilbertTest f d T :=
  prod.lift b k

/-- The point of the original Picard sheaf, translated on its actual parameter base. -/
def variableHilbertPoint (c : (relativeFppfSheaf f).obj.obj (op T))
    (U : Over (Spec (.of R))) (k : U ⟶ variableHilbertTest f d T) :
    (relativeFppfSheaf f).obj.obj (op U) :=
  (show (relativeFppfSheaf f).obj.obj (op U) from
    acyclicHilbertPicardPoint f d hB U (k ≫ variableHilbertParameter f d T)) /
    (relativeFppfSheaf f).obj.map (k ≫ variableHilbertBase f d T).op c

/-- The two supplied maps retain exactly their original translated class. -/
theorem variableHilbertPoint_lift (c : (relativeFppfSheaf f).obj.obj (op T))
    {U : Over (Spec (.of R))} (b : U ⟶ T) (k : U ⟶ acyclicHilbertTest f d) :
    variableHilbertPoint f d hB T c U (variableHilbertLift f d T b k) =
      (show (relativeFppfSheaf f).obj.obj (op U) from acyclicHilbertPicardPoint f d hB U k) /
        (relativeFppfSheaf f).obj.map b.op c := by
  simp only [variableHilbertPoint, variableHilbertLift, variableHilbertBase,
    variableHilbertParameter, prod.lift_fst, prod.lift_snd]

/-- The chart map is natural for every original test morphism. -/
theorem variableHilbertPoint_natural (c : (relativeFppfSheaf f).obj.obj (op T))
    {U V : Over (Spec (.of R))} (b : V ⟶ U) (k : U ⟶ variableHilbertTest f d T) :
    variableHilbertPoint f d hB T c V (b ≫ k) =
      (relativeFppfSheaf f).obj.map b.op (variableHilbertPoint f d hB T c U k) := by
  simp only [variableHilbertPoint, Category.assoc, acyclicHilbertPicardPoint_natural,
    map_div, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

/-- Over a fixed parameter-base map, the original class determines the entire chart map. -/
theorem variableHilbertPoint_injective_over (c : (relativeFppfSheaf f).obj.obj (op T))
    {U : Over (Spec (.of R))} {k l : U ⟶ variableHilbertTest f d T}
    (hb : k ≫ variableHilbertBase f d T = l ≫ variableHilbertBase f d T)
    (hc : variableHilbertPoint f d hB T c U k = variableHilbertPoint f d hB T c U l) :
    k = l := by
  apply prod.hom_ext
  · exact hb
  · unfold variableHilbertPoint at hc
    rw [hb, div_left_inj] at hc
    exact acyclicHilbertPicardPoint_injective f d hB U hc

/-- A translation restricted from the original fixed base recovers the earlier chart formula. -/
theorem variableHilbertPoint_of_base
    (c : (relativeFppfSheaf f).obj.obj (op (Over.mk (𝟙 (Spec (.of R))))))
    {U : Over (Spec (.of R))} (k : U ⟶ variableHilbertTest f d T) :
    variableHilbertPoint f d hB T (basePicardSection f c T) U k =
      translatedHilbertPicardPoint f d hB c U (k ≫ variableHilbertParameter f d T) := by
  unfold variableHilbertPoint translatedHilbertPicardPoint
  rw [basePicardSection_natural]

end FLT.Mazur.HilbertChart
