/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThreeFiniteNodes
public import FLT.Mazur.WeierstrassDividedFifthFartherGeometry

/-!
# Finite geometry for the initial open, all four retained nodes and common terminal

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
  (H : ArithmeticAtlasCoefficients data) (k m : ℕ) (hj : 4 ≤ n)
  (u : Rˣ) (hu : (data ⟨4, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "e" => arithmeticFifthFartherSmoothing hπ data H 3 hj u hu m
local notation "s" => PolygonArithmeticRetainedChain.State.retained
  (arithmeticThreeSeedState hπ data H hj u hu) m

/-- The whole initial node changes from its exact fifth smoothing to its finite smoothing. -/
def arithmeticThreeFiniteInitialNodeIso (b : Bool) :
    PolygonSmoothing.chart Q (e b) ≅
      PolygonSmoothing.chart Q ((arithmeticThreeFiniteState hπ data H hj u hu k).initial m b) :=
  Scheme.Spec.mapIso
    (arithmeticThreeFiniteInitialFactor hπ data H hj u hu k m b).toRingEquiv.toCommRingCatIso.op

/-- Each retained node uses the full correction from both incident edges. -/
def arithmeticThreeFiniteRetainedIso (i : Fin 4) (b : Bool) :
    PolygonSmoothing.chart Q (s i b) ≅ PolygonSmoothing.chart Q
      ((arithmeticThreeFiniteState hπ data H hj u hu k).retained m i b) :=
  Scheme.Spec.mapIso
    (arithmeticThreeFiniteRetainedFactor hπ data H hj u hu k m i b).toRingEquiv.toCommRingCatIso.op

/-- Both initial punctures are induced by the same whole node factor. -/
@[reassoc] theorem arithmeticThreeFiniteInitialNodeIso_puncture (b a : Bool) :
    punctureOpen (e b) a ≫ (arithmeticThreeFiniteInitialNodeIso hπ data H k m hj u hu b).hom =
      (punctureSpecIso (arithmeticThreeFiniteInitialPunctureEquiv hπ data H hj u hu k m b a)).hom ≫
        punctureOpen ((arithmeticThreeFiniteState hπ data H hj u hu k).initial m b) a := by
  apply punctureFactor_spec
  exact arithmeticThreeFiniteInitialFactor_puncture hπ data H hj u hu k m b a

/-- Both retained punctures retain their full simultaneous correction. -/
@[reassoc] theorem arithmeticThreeFiniteRetainedIso_puncture (i : Fin 4) (b a : Bool) :
    punctureOpen (s i b) a ≫ (arithmeticThreeFiniteRetainedIso hπ data H k m hj u hu i b).hom =
      (punctureSpecIso
        (arithmeticThreeFiniteRetainedPunctureEquiv hπ data H hj u hu k m i b a)).hom ≫
        punctureOpen ((arithmeticThreeFiniteState hπ data H hj u hu k).retained m i b) a := by
  apply punctureFactor_spec
  exact arithmeticThreeFiniteRetainedFactor_puncture hπ data H hj u hu k m i b a

local notation "C" => arithmeticThreeFiniteInitialNodeIso hπ data H k m hj u hu
local notation "M" => arithmeticFifthFartherNodeChart hπ data H m 3 hj u hu
local notation "A" => fun b ↦ punctureSpecIso
  (arithmeticThreeFiniteInitialPunctureEquiv hπ data H hj u hu k m b true)

/-- Pull the actual fifth initial open through the full finite node comparison. -/
def arithmeticThreeFiniteInitialObject (b : Bool) : Scheme := pullback (C b).inv (M b)

/-- The fifth initial open is isomorphic to the constructed finite initial open. -/
def arithmeticThreeFiniteInitialIso (b : Bool) :
    arithmeticFifthFartherObject hπ data H m 3 hj u hu b ≅
      arithmeticThreeFiniteInitialObject hπ data H k m hj u hu b :=
  (asIso (pullback.snd (C b).inv (M b))).symm

local notation "I" => arithmeticThreeFiniteInitialIso hπ data H k m hj u hu

/-- The corrected initial open maps into its full changed-smoothing node. -/
def arithmeticThreeFiniteInitialNodeChart (b : Bool) :
    arithmeticThreeFiniteInitialObject hπ data H k m hj u hu b ⟶
      PolygonSmoothing.chart Q ((arithmeticThreeFiniteState hπ data H hj u hu k).initial m b) :=
  pullback.fst (C b).inv (M b)

local notation "F" => arithmeticThreeFiniteInitialNodeChart hπ data H k m hj u hu

instance arithmeticThreeFiniteInitialNodeChart_isOpenImmersion (b : Bool) :
    IsOpenImmersion (F b) := by
  unfold arithmeticThreeFiniteInitialNodeChart
  infer_instance

/-- The full initial comparison commutes with its actual fifth and finite node maps. -/
@[reassoc] theorem arithmeticThreeFiniteInitialIso_nodeChart (b : Bool) :
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
def arithmeticThreeFiniteInitialPuncture (b : Bool) :
    branchTorus Q ⟶ arithmeticThreeFiniteInitialObject hπ data H k m hj u hu b :=
  (A b).inv ≫ arithmeticFifthFartherPuncture hπ data H m 3 hj u hu b ≫ (I b).hom

/-- The puncture of the corrected initial open is the standard puncture of its new node. -/
@[reassoc] theorem arithmeticThreeFiniteInitialPuncture_nodeChart (b : Bool) :
    arithmeticThreeFiniteInitialPuncture hπ data H k m hj u hu b ≫ F b =
      leftBranchOpen Q ((arithmeticThreeFiniteState hπ data H hj u hu k).initial m b) := by
  simp only [arithmeticThreeFiniteInitialPuncture, Category.assoc,
    arithmeticThreeFiniteInitialIso_nodeChart]
  rw [arithmeticFifthFartherPuncture_nodeChart_assoc]
  have h := arithmeticThreeFiniteInitialNodeIso_puncture hπ data H k m hj u hu b true
  simp only [punctureOpen_true] at h
  rw [h, Iso.inv_hom_id_assoc]

local notation "T" => arithmeticThreeFiniteTerminalFactor hπ data H hj u hu k m

/-- The common terminal is transported by the inverse of its full rebased factor. -/
def arithmeticThreeFiniteTerminalIso :
    PolygonSmoothing.chart Q (arithmeticFifthShallowTerminalSmoothing hπ data H 3 hj u hu m) ≅
      PolygonSmoothing.chart Q ((arithmeticThreeFiniteState hπ data H hj u hu k).terminal m) :=
  (Scheme.Spec.mapIso (T).toRingEquiv.toCommRingCatIso.op).symm

/-- Both inverse punctures come from the same full common terminal comparison. -/
@[reassoc] theorem arithmeticThreeFiniteTerminalIso_puncture (b : Bool) :
    punctureOpen (arithmeticFifthShallowTerminalSmoothing hπ data H 3 hj u hu m) b ≫
        (arithmeticThreeFiniteTerminalIso hπ data H k m hj u hu).hom =
      (punctureSpecIso
        (arithmeticThreeFiniteTerminalPunctureEquiv hπ data H hj u hu k m b).symm).hom ≫
          punctureOpen ((arithmeticThreeFiniteState hπ data H hj u hu k).terminal m) b := by
  apply punctureFactor_spec _ _ (T).symm
  apply punctureFactor_symm
  exact arithmeticThreeFiniteTerminalFactor_puncture hπ data H hj u hu k m b

end FLT.Mazur.WeierstrassDividedDepth
