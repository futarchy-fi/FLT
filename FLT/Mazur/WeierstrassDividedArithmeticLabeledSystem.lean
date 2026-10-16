/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLabeledAtlasRestriction
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# The full labeled arithmetic diagram at all quotient orders

The actual original global stages and each fixed chart label form functors.
Their original chart maps are natural for every pair of quotient orders,
including nonadjacent orders, without changing the containing resolution stage.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (H : ArithmeticAtlasCoefficients data) (k : ℕ) (hk : k ≤ n)

/-- The original global quotient stages at one fixed resolution depth. -/
def finiteGlobalArithmeticSystem : ℕ ⥤ Scheme :=
  Functor.ofSequence (finiteGlobalArithmeticRestriction hπ data k hk)

/-- One original full labeled chart at all arithmetic orders. -/
def arithmeticLabeledChartSystem (i : ArithmeticChartLabel k) : ℕ ⥤ Scheme :=
  Functor.ofSequence (fun m => arithmeticLabeledAtlasRestriction hπ data H m k hk i)

/-- The complete labeled chart map is natural for the original arithmetic quotient diagram. -/
def arithmeticLabeledChartSystemMap (i : ArithmeticChartLabel k) :
    arithmeticLabeledChartSystem hπ data H k hk i ⟶ finiteGlobalArithmeticSystem hπ data k hk :=
  NatTrans.ofSequence (fun m => arithmeticLabeledAtlasMap hπ data H m k hk i) (by
    intro m
    simpa only [arithmeticLabeledChartSystem, finiteGlobalArithmeticSystem,
      Functor.ofSequence_obj, Functor.ofSequence_map_homOfLE_succ] using
        arithmeticLabeledAtlasMap_restriction hπ data H m k hk i)

/-- Every pair of quotient orders has its original full labeled chart square. -/
@[reassoc] theorem arithmeticLabeledChartSystemMap_naturality
    (i : ArithmeticChartLabel k) {a b : ℕ} (hab : a ≤ b) :
    (arithmeticLabeledChartSystem hπ data H k hk i).map (homOfLE hab) ≫
      arithmeticLabeledAtlasMap hπ data H b k hk i =
        arithmeticLabeledAtlasMap hπ data H a k hk i ≫
          (finiteGlobalArithmeticSystem hπ data k hk).map (homOfLE hab) :=
  (arithmeticLabeledChartSystemMap hπ data H k hk i).naturality (homOfLE hab)

/-- The original global quotient system retains its integral model at every order. -/
def finiteGlobalArithmeticSystemProjection :
    finiteGlobalArithmeticSystem hπ data k hk ⟶
      (Functor.const ℕ).obj (finiteGlobalModel hπ data k hk) :=
  NatTrans.ofSequence (finiteGlobalArithmeticProjection hπ data k hk) (by
    intro m
    change (Functor.ofSequence (finiteGlobalArithmeticRestriction hπ data k hk)).map
      (homOfLE (Nat.le_succ m)) ≫ finiteGlobalArithmeticProjection hπ data k hk (m + 1) =
        finiteGlobalArithmeticProjection hπ data k hk m ≫ 𝟙 _
    rw [Functor.ofSequence_map_homOfLE_succ, Category.comp_id,
      finiteGlobalArithmeticRestriction_projection])

/-- The actual quotient coefficient spectra form the base of the whole global system. -/
def finiteGlobalArithmeticSystemStructure :
    finiteGlobalArithmeticSystem hπ data k hk ⟶ baseSystem R π :=
  NatTrans.ofSequence (finiteGlobalArithmeticStructure hπ data k hk) (by
    intro m
    simpa only [finiteGlobalArithmeticSystem, baseSystem, Functor.ofSequence_obj,
      Functor.ofSequence_map_homOfLE_succ] using
        finiteGlobalArithmeticRestriction_structure hπ data k hk m)

end FLT.Mazur.WeierstrassDividedDepth
