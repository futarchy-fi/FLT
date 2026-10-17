/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalChangedAtlas
public import FLT.Mazur.WeierstrassDividedTerminalChangedRestriction
public import FLT.Mazur.WeierstrassDividedTwistedAtlasRestriction

/-!
# The revised labeled arithmetic atlas at every quotient order

The changed terminal smoothing uses its explicit coefficient restriction.
All other chart restrictions and all original labels are retained. The full
chart maps are natural even for nonconsecutive arithmetic orders.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "A" => fun m ↦ changedArithmeticAtlasObject hπ data H m j hj u hu
local notation "J" => fun m ↦ changedArithmeticAtlasToTwisted hπ data H m j hj u hu
local notation "κ" => fun m ↦ changedArithmeticAtlasChart hπ data H m j hj u hu
local notation "ρ" => fun m ↦ twistedArithmeticAtlasRestriction hπ data H m j hj
local notation "q" => simultaneousTwistedArithmeticRestriction hπ data H
local notation "G" => fun m ↦ simultaneousTwistedArithmeticIso hπ data H m j hj u hu

/-- Only the terminal quotient arrow changes, by its explicit revised coefficient map. -/
def changedArithmeticAtlasRestriction (m : ℕ) (i : ArithmeticChartLabel (j + 1)) :
    A m i ⟶ A (m + 1) i :=
  match i with
  | .terminal => arithmeticTerminalChangedRestriction hπ data H m j hj u hu
  | .retained idx b => ρ m (.retained idx b)
  | .infinity => ρ m .infinity
  | .initial b => ρ m (.initial b)

local notation "S" => changedArithmeticAtlasRestriction hπ data H j hj u hu

omit [IsBezout R] in
/-- Each revised chart comparison respects the actual original coefficient arrow. -/
@[reassoc] theorem changedArithmeticAtlasToTwisted_restriction
    (m : ℕ) (i : ArithmeticChartLabel (j + 1)) :
    S m i ≫ (J (m + 1) i).hom = (J m i).hom ≫ ρ m i := by
  cases i with
  | terminal => exact (arithmeticTerminalChangedIso_inv_restriction hπ data H m j hj u hu).symm
  | retained idx b => exact (Category.comp_id _).trans (Category.id_comp _).symm
  | infinity => exact (Category.comp_id _).trans (Category.id_comp _).symm
  | initial b => exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- The full revised labeled inclusion commutes with the global arithmetic quotient arrow. -/
@[reassoc] theorem changedArithmeticAtlasChart_restriction
    (m : ℕ) (i : ArithmeticChartLabel (j + 1)) :
    S m i ≫ κ (m + 1) i = κ m i ≫ q m j hj u hu := by
  dsimp only
  rw [changedArithmeticAtlasChart, changedArithmeticAtlasChart, ← Category.assoc,
    changedArithmeticAtlasToTwisted_restriction, Category.assoc,
    simultaneousTwistedArithmeticChart_restriction, Category.assoc]

/-- The complete global target with its unchanged arithmetic quotient arrows. -/
def changedArithmeticTargetSystem : ℕ ⥤ Scheme :=
  Functor.ofSequence (fun m ↦ q m j hj u hu)

/-- One full revised labeled chart at all arithmetic orders. -/
def changedArithmeticChartSystem (i : ArithmeticChartLabel (j + 1)) : ℕ ⥤ Scheme :=
  Functor.ofSequence (fun m ↦ S m i)

/-- The revised full chart map is natural for the original arithmetic order diagram. -/
def changedArithmeticChartSystemMap (i : ArithmeticChartLabel (j + 1)) :
    changedArithmeticChartSystem hπ data H j hj u hu i ⟶
      changedArithmeticTargetSystem hπ data H j hj u hu :=
  NatTrans.ofSequence (fun m ↦ κ m i) (by
    intro m
    simpa only [changedArithmeticChartSystem, changedArithmeticTargetSystem,
      Functor.ofSequence_obj, Functor.ofSequence_map_homOfLE_succ] using
        changedArithmeticAtlasChart_restriction hπ data H j hj u hu m i)

/-- Every nonconsecutive quotient also preserves the full revised labeled chart. -/
@[reassoc] theorem changedArithmeticChartSystemMap_naturality
    (i : ArithmeticChartLabel (j + 1)) {a b : ℕ} (hab : a ≤ b) :
    (changedArithmeticChartSystem hπ data H j hj u hu i).map (homOfLE hab) ≫ κ b i =
      κ a i ≫ (changedArithmeticTargetSystem hπ data H j hj u hu).map (homOfLE hab) :=
  (changedArithmeticChartSystemMap hπ data H j hj u hu i).naturality (homOfLE hab)

/-- The original complete model maps naturally to this target at every arithmetic order. -/
def changedArithmeticGlobalSystemMap :
    finiteGlobalArithmeticSystem hπ data (j + 1) hj ⟶
      changedArithmeticTargetSystem hπ data H j hj u hu :=
  NatTrans.ofSequence (fun m ↦ (G m).hom) (by
    intro m
    simpa only [finiteGlobalArithmeticSystem, changedArithmeticTargetSystem,
      Functor.ofSequence_obj, Functor.ofSequence_map_homOfLE_succ] using
        (simultaneousTwistedArithmeticIso_restriction hπ data H m j hj u hu).symm)

instance changedArithmeticGlobalSystemMap_isIso :
    IsIso (changedArithmeticGlobalSystemMap hπ data H j hj u hu) := by
  let _ : ∀ m, IsIso ((changedArithmeticGlobalSystemMap hπ data H j hj u hu).app m) :=
    fun m ↦ by
      change IsIso (G m).hom
      infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- The global system comparison is an isomorphism, without identifying a standard polygon. -/
def changedArithmeticGlobalSystemIso :
    finiteGlobalArithmeticSystem hπ data (j + 1) hj ≅
      changedArithmeticTargetSystem hπ data H j hj u hu :=
  asIso (changedArithmeticGlobalSystemMap hπ data H j hj u hu)

end FLT.Mazur.WeierstrassDividedDepth
