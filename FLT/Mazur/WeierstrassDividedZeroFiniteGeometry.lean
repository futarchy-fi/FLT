/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroFiniteNodes
public import FLT.Mazur.WeierstrassDividedZeroFifthGeometry

/-!
# Finite geometry for the initial open, shared last node and common terminal

The full initial open is pulled through its finite factor from its actual
fifth smoothing. The last full factor starts on that last node's fifth smoothing.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (k m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "e" => arithmeticZeroFifthInitialSmoothing hπ data H j hj u hu m
local notation "s" => arithmeticZeroFifthLastSmoothing hπ data H j hj u hu m

/-- The whole initial node changes from its exact fifth smoothing to its finite. -/
def arithmeticZeroFiniteInitialNodeIso (b : Bool) :
    PolygonSmoothing.chart Q (e b) ≅
      PolygonSmoothing.chart Q ((arithmeticZeroFiniteState hπ data H j hj u hu k).initial m b) :=
  Scheme.Spec.mapIso
    (arithmeticZeroFiniteInitialFactor hπ data H j hj u hu k m b).toRingEquiv.toCommRingCatIso.op

/-- The last node uses the simultaneous initial and incoming correction. -/
def arithmeticZeroFiniteLastIso (b : Bool) :
    PolygonSmoothing.chart Q (s b) ≅ PolygonSmoothing.chart Q
      ((arithmeticZeroFiniteState hπ data H j hj u hu k).last m b) :=
  Scheme.Spec.mapIso
    (arithmeticZeroFiniteLastFactor hπ data H j hj u hu k m b).toRingEquiv.toCommRingCatIso.op

/-- Both initial punctures are induced by the same whole node factor. -/
@[reassoc] theorem arithmeticZeroFiniteInitialNodeIso_puncture (b a : Bool) :
    punctureOpen (e b) a ≫ (arithmeticZeroFiniteInitialNodeIso hπ data H k m j hj u hu b).hom =
      (punctureSpecIso (arithmeticZeroFiniteInitialPunctureEquiv hπ data H j hj u hu k m b a)).hom ≫
        punctureOpen ((arithmeticZeroFiniteState hπ data H j hj u hu k).initial m b) a := by
  apply punctureFactor_spec
  exact arithmeticZeroFiniteInitialFactor_puncture hπ data H j hj u hu k m b a

/-- Both last punctures retain their full simultaneous correction. -/
@[reassoc] theorem arithmeticZeroFiniteLastIso_puncture (b a : Bool) :
    punctureOpen (s b) a ≫ (arithmeticZeroFiniteLastIso hπ data H k m j hj u hu b).hom =
      (punctureSpecIso (arithmeticZeroFiniteLastPunctureEquiv hπ data H j hj u hu k m b a)).hom ≫
        punctureOpen ((arithmeticZeroFiniteState hπ data H j hj u hu k).last m b) a := by
  apply punctureFactor_spec
  exact arithmeticZeroFiniteLastFactor_puncture hπ data H j hj u hu k m b a

local notation "C" => arithmeticZeroFiniteInitialNodeIso hπ data H k m j hj u hu
local notation "M" => arithmeticZeroFifthInitialNodeChart hπ data H m j hj u hu
local notation "A" => fun b ↦ punctureSpecIso
  (arithmeticZeroFiniteInitialPunctureEquiv hπ data H j hj u hu k m b true)

/-- Pull the actual fifth initial open through the full finite node comparison. -/
def arithmeticZeroFiniteInitialObject (b : Bool) : Scheme := pullback (C b).inv (M b)

/-- The fifth initial open is isomorphic to the constructed finite initial open. -/
def arithmeticZeroFiniteInitialIso (b : Bool) :
    arithmeticZeroFifthInitialObject hπ data H m j hj u hu b ≅
      arithmeticZeroFiniteInitialObject hπ data H k m j hj u hu b :=
  (asIso (pullback.snd (C b).inv (M b))).symm

local notation "I" => arithmeticZeroFiniteInitialIso hπ data H k m j hj u hu

/-- The corrected initial open maps into its full changed-smoothing node. -/
def arithmeticZeroFiniteInitialNodeChart (b : Bool) :
    arithmeticZeroFiniteInitialObject hπ data H k m j hj u hu b ⟶
      PolygonSmoothing.chart Q ((arithmeticZeroFiniteState hπ data H j hj u hu k).initial m b) :=
  pullback.fst (C b).inv (M b)

local notation "F" => arithmeticZeroFiniteInitialNodeChart hπ data H k m j hj u hu

instance arithmeticZeroFiniteInitialNodeChart_isOpenImmersion (b : Bool) :
    IsOpenImmersion (F b) := by
  unfold arithmeticZeroFiniteInitialNodeChart
  infer_instance

/-- The full initial comparison commutes with its actual fifth and finite node maps. -/
@[reassoc] theorem arithmeticZeroFiniteInitialIso_nodeChart (b : Bool) :
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
def arithmeticZeroFiniteInitialPuncture (b : Bool) :
    branchTorus Q ⟶ arithmeticZeroFiniteInitialObject hπ data H k m j hj u hu b :=
  (A b).inv ≫ arithmeticZeroFifthInitialPuncture hπ data H m j hj u hu b ≫ (I b).hom

/-- The puncture of the corrected initial open is the standard puncture of its new node. -/
@[reassoc] theorem arithmeticZeroFiniteInitialPuncture_nodeChart (b : Bool) :
    arithmeticZeroFiniteInitialPuncture hπ data H k m j hj u hu b ≫ F b =
      leftBranchOpen Q ((arithmeticZeroFiniteState hπ data H j hj u hu k).initial m b) := by
  simp only [arithmeticZeroFiniteInitialPuncture, Category.assoc,
    arithmeticZeroFiniteInitialIso_nodeChart]
  rw [arithmeticZeroFifthInitialPuncture_nodeChart_assoc]
  have h := arithmeticZeroFiniteInitialNodeIso_puncture hπ data H k m j hj u hu b true
  simp only [punctureOpen_true] at h
  rw [h, Iso.inv_hom_id_assoc]

local notation "T" => arithmeticZeroFiniteTerminalFactor hπ data H j hj u hu k m

/-- The common terminal is transported by the inverse of its full rebased factor. -/
def arithmeticZeroFiniteTerminalIso :
    PolygonSmoothing.chart Q (arithmeticZeroFifthTerminalSmoothing hπ data H j hj u hu m) ≅
      PolygonSmoothing.chart Q ((arithmeticZeroFiniteState hπ data H j hj u hu k).terminal m) :=
  (Scheme.Spec.mapIso (T).toRingEquiv.toCommRingCatIso.op).symm

/-- Both inverse punctures come from the same full common terminal comparison. -/
@[reassoc] theorem arithmeticZeroFiniteTerminalIso_puncture (b : Bool) :
    punctureOpen (arithmeticZeroFifthTerminalSmoothing hπ data H j hj u hu m) b ≫
        (arithmeticZeroFiniteTerminalIso hπ data H k m j hj u hu).hom =
      (punctureSpecIso
        (arithmeticZeroFiniteTerminalPunctureEquiv hπ data H j hj u hu k m b).symm).hom ≫
          punctureOpen ((arithmeticZeroFiniteState hπ data H j hj u hu k).terminal m) b := by
  apply punctureFactor_spec _ _ (T).symm
  apply punctureFactor_symm
  exact arithmeticZeroFiniteTerminalFactor_puncture hπ data H j hj u hu k m b

end FLT.Mazur.WeierstrassDividedDepth
