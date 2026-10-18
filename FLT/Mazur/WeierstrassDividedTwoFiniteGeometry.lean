/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTwoFiniteNodes
public import FLT.Mazur.WeierstrassDividedFifthShallowGeometry

/-!
# Finite geometry for the initial open, all three retained nodes and common terminal

The full initial open is pulled through its finite factor from its actual
fifth smoothing. Each retained factor starts on its own exact fifth smoothing.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (k m : ℕ) (hj : 3 ≤ n)
  (u : Rˣ) (hu : (data ⟨3, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "e" => arithmeticFifthShallowSmoothing hπ data H 2 hj u hu m
local notation "s" => PolygonArithmeticRetainedChain.State.retained
  (arithmeticTwoSeedState hπ data H hj u hu) m

/-- The whole initial node changes from its exact fifth smoothing to its finite smoothing. -/
def arithmeticTwoFiniteInitialNodeIso (b : Bool) :
    PolygonSmoothing.chart Q (e b) ≅
      PolygonSmoothing.chart Q ((arithmeticTwoFiniteState hπ data H hj u hu k).initial m b) :=
  Scheme.Spec.mapIso
    (arithmeticTwoFiniteInitialFactor hπ data H hj u hu k m b).toRingEquiv.toCommRingCatIso.op

/-- Each retained node uses the full correction from both incident edges. -/
def arithmeticTwoFiniteRetainedIso (i : Fin 3) (b : Bool) :
    PolygonSmoothing.chart Q (s i b) ≅ PolygonSmoothing.chart Q
      ((arithmeticTwoFiniteState hπ data H hj u hu k).retained m i b) :=
  Scheme.Spec.mapIso
    (arithmeticTwoFiniteRetainedFactor hπ data H hj u hu k m i b).toRingEquiv.toCommRingCatIso.op

/-- Both initial punctures are induced by the same whole node factor. -/
@[reassoc] theorem arithmeticTwoFiniteInitialNodeIso_puncture (b a : Bool) :
    punctureOpen (e b) a ≫ (arithmeticTwoFiniteInitialNodeIso hπ data H k m hj u hu b).hom =
      (punctureSpecIso (arithmeticTwoFiniteInitialPunctureEquiv hπ data H hj u hu k m b a)).hom ≫
        punctureOpen ((arithmeticTwoFiniteState hπ data H hj u hu k).initial m b) a := by
  apply punctureFactor_spec
  exact arithmeticTwoFiniteInitialFactor_puncture hπ data H hj u hu k m b a

/-- Both retained punctures retain their full simultaneous correction. -/
@[reassoc] theorem arithmeticTwoFiniteRetainedIso_puncture (i : Fin 3) (b a : Bool) :
    punctureOpen (s i b) a ≫ (arithmeticTwoFiniteRetainedIso hπ data H k m hj u hu i b).hom =
      (punctureSpecIso (arithmeticTwoFiniteRetainedPunctureEquiv hπ data H hj u hu k m i b a)).hom ≫
        punctureOpen ((arithmeticTwoFiniteState hπ data H hj u hu k).retained m i b) a := by
  apply punctureFactor_spec
  exact arithmeticTwoFiniteRetainedFactor_puncture hπ data H hj u hu k m i b a

local notation "C" => arithmeticTwoFiniteInitialNodeIso hπ data H k m hj u hu
local notation "M" => arithmeticFifthShallowNodeChart hπ data H m 2 hj u hu
local notation "A" => fun b ↦ punctureSpecIso
  (arithmeticTwoFiniteInitialPunctureEquiv hπ data H hj u hu k m b true)

/-- Pull the actual fifth initial open through the full finite node comparison. -/
def arithmeticTwoFiniteInitialObject (b : Bool) : Scheme := pullback (C b).inv (M b)

/-- The fifth initial open is isomorphic to the constructed finite initial open. -/
def arithmeticTwoFiniteInitialIso (b : Bool) :
    arithmeticFifthShallowObject hπ data H m 2 hj u hu b ≅
      arithmeticTwoFiniteInitialObject hπ data H k m hj u hu b :=
  (asIso (pullback.snd (C b).inv (M b))).symm

local notation "I" => arithmeticTwoFiniteInitialIso hπ data H k m hj u hu

/-- The corrected initial open maps into its full changed-smoothing node. -/
def arithmeticTwoFiniteInitialNodeChart (b : Bool) :
    arithmeticTwoFiniteInitialObject hπ data H k m hj u hu b ⟶
      PolygonSmoothing.chart Q ((arithmeticTwoFiniteState hπ data H hj u hu k).initial m b) :=
  pullback.fst (C b).inv (M b)

local notation "F" => arithmeticTwoFiniteInitialNodeChart hπ data H k m hj u hu

instance arithmeticTwoFiniteInitialNodeChart_isOpenImmersion (b : Bool) :
    IsOpenImmersion (F b) := by
  unfold arithmeticTwoFiniteInitialNodeChart
  infer_instance

/-- The full initial comparison commutes with its actual fifth and finite node maps. -/
@[reassoc] theorem arithmeticTwoFiniteInitialIso_nodeChart (b : Bool) :
    (I b).hom ≫ F b = M b ≫ (C b).hom := by
  apply (cancel_mono (C b).inv).mp
  rw [Category.assoc]
  change (asIso (pullback.snd (C b).inv (M b))).inv ≫
    pullback.fst (C b).inv (M b) ≫ (C b).inv = _
  rw [pullback.condition]
  have hi := (asIso (pullback.snd (C b).inv (M b))).inv_hom_id
  simpa only [asIso_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Category.id_comp] using congrArg (fun f ↦ f ≫ M b) hi

/-- Transport the actual fifth puncture with the finite initial substitution. -/
def arithmeticTwoFiniteInitialPuncture (b : Bool) :
    branchTorus Q ⟶ arithmeticTwoFiniteInitialObject hπ data H k m hj u hu b :=
  (A b).inv ≫ arithmeticFifthShallowPuncture hπ data H m 2 hj u hu b ≫ (I b).hom

/-- The puncture of the corrected initial open is the standard puncture of its new node. -/
@[reassoc] theorem arithmeticTwoFiniteInitialPuncture_nodeChart (b : Bool) :
    arithmeticTwoFiniteInitialPuncture hπ data H k m hj u hu b ≫ F b =
      leftBranchOpen Q ((arithmeticTwoFiniteState hπ data H hj u hu k).initial m b) := by
  simp only [arithmeticTwoFiniteInitialPuncture, Category.assoc,
    arithmeticTwoFiniteInitialIso_nodeChart]
  rw [arithmeticFifthShallowPuncture_nodeChart_assoc]
  have h := arithmeticTwoFiniteInitialNodeIso_puncture hπ data H k m hj u hu b true
  simp only [punctureOpen_true] at h
  rw [h, Iso.inv_hom_id_assoc]

local notation "T" => arithmeticTwoFiniteTerminalFactor hπ data H hj u hu k m

/-- The common terminal is transported by the inverse of its full rebased factor. -/
def arithmeticTwoFiniteTerminalIso :
    PolygonSmoothing.chart Q (arithmeticFifthShallowTerminalSmoothing hπ data H 2 hj u hu m) ≅
      PolygonSmoothing.chart Q ((arithmeticTwoFiniteState hπ data H hj u hu k).terminal m) :=
  (Scheme.Spec.mapIso (T).toRingEquiv.toCommRingCatIso.op).symm

/-- Both inverse punctures come from the same full common terminal comparison. -/
@[reassoc] theorem arithmeticTwoFiniteTerminalIso_puncture (b : Bool) :
    punctureOpen (arithmeticFifthShallowTerminalSmoothing hπ data H 2 hj u hu m) b ≫
        (arithmeticTwoFiniteTerminalIso hπ data H k m hj u hu).hom =
      (punctureSpecIso
        (arithmeticTwoFiniteTerminalPunctureEquiv hπ data H hj u hu k m b).symm).hom ≫
          punctureOpen ((arithmeticTwoFiniteState hπ data H hj u hu k).terminal m) b := by
  apply punctureFactor_spec _ _ (T).symm
  apply punctureFactor_symm
  exact arithmeticTwoFiniteTerminalFactor_puncture hπ data H hj u hu k m b

end FLT.Mazur.WeierstrassDividedDepth
