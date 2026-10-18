/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOneFiniteNodes
public import FLT.Mazur.WeierstrassDividedFifthInitialGeometry

/-!
# Finite geometry for the initial open, both retained nodes and common terminal

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
  (H : ArithmeticAtlasCoefficients data) (k m : ℕ) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "e" => arithmeticFifthInitialSmoothing hπ data H 1 hj u hu m
local notation "s" => PolygonArithmeticRetainedChain.State.retained
  (arithmeticOneSeedState hπ data H hj u hu) m

/-- The whole initial node changes from its exact fifth smoothing to its finite smoothing. -/
def arithmeticOneFiniteInitialNodeIso (b : Bool) :
    PolygonSmoothing.chart Q (e b) ≅
      PolygonSmoothing.chart Q ((arithmeticOneFiniteState hπ data H hj u hu k).initial m b) :=
  Scheme.Spec.mapIso
    (arithmeticOneFiniteInitialFactor hπ data H hj u hu k m b).toRingEquiv.toCommRingCatIso.op

/-- The last node uses the simultaneous initial and incoming correction. -/
def arithmeticOneFiniteRetainedIso (i : Fin 2) (b : Bool) :
    PolygonSmoothing.chart Q (s i b) ≅ PolygonSmoothing.chart Q
      ((arithmeticOneFiniteState hπ data H hj u hu k).retained m i b) :=
  Scheme.Spec.mapIso
    (arithmeticOneFiniteRetainedFactor hπ data H hj u hu k m i b).toRingEquiv.toCommRingCatIso.op

/-- Both initial punctures are induced by the same whole node factor. -/
@[reassoc] theorem arithmeticOneFiniteInitialNodeIso_puncture (b a : Bool) :
    punctureOpen (e b) a ≫ (arithmeticOneFiniteInitialNodeIso hπ data H k m hj u hu b).hom =
      (punctureSpecIso (arithmeticOneFiniteInitialPunctureEquiv hπ data H hj u hu k m b a)).hom ≫
        punctureOpen ((arithmeticOneFiniteState hπ data H hj u hu k).initial m b) a := by
  apply punctureFactor_spec
  exact arithmeticOneFiniteInitialFactor_puncture hπ data H hj u hu k m b a

/-- Both retained punctures retain their full simultaneous correction. -/
@[reassoc] theorem arithmeticOneFiniteRetainedIso_puncture (i : Fin 2) (b a : Bool) :
    punctureOpen (s i b) a ≫ (arithmeticOneFiniteRetainedIso hπ data H k m hj u hu i b).hom =
      (punctureSpecIso (arithmeticOneFiniteRetainedPunctureEquiv hπ data H hj u hu k m i b a)).hom ≫
        punctureOpen ((arithmeticOneFiniteState hπ data H hj u hu k).retained m i b) a := by
  apply punctureFactor_spec
  exact arithmeticOneFiniteRetainedFactor_puncture hπ data H hj u hu k m i b a

local notation "C" => arithmeticOneFiniteInitialNodeIso hπ data H k m hj u hu
local notation "M" => arithmeticFifthInitialNodeChart hπ data H m 1 hj u hu
local notation "A" => fun b ↦ punctureSpecIso
  (arithmeticOneFiniteInitialPunctureEquiv hπ data H hj u hu k m b true)

/-- Pull the actual fifth initial open through the full finite node comparison. -/
def arithmeticOneFiniteInitialObject (b : Bool) : Scheme := pullback (C b).inv (M b)

/-- The fifth initial open is isomorphic to the constructed finite initial open. -/
def arithmeticOneFiniteInitialIso (b : Bool) :
    arithmeticFifthInitialObject hπ data H m 1 hj u hu b ≅
      arithmeticOneFiniteInitialObject hπ data H k m hj u hu b :=
  (asIso (pullback.snd (C b).inv (M b))).symm

local notation "I" => arithmeticOneFiniteInitialIso hπ data H k m hj u hu

/-- The corrected initial open maps into its full changed-smoothing node. -/
def arithmeticOneFiniteInitialNodeChart (b : Bool) :
    arithmeticOneFiniteInitialObject hπ data H k m hj u hu b ⟶
      PolygonSmoothing.chart Q ((arithmeticOneFiniteState hπ data H hj u hu k).initial m b) :=
  pullback.fst (C b).inv (M b)

local notation "F" => arithmeticOneFiniteInitialNodeChart hπ data H k m hj u hu

instance arithmeticOneFiniteInitialNodeChart_isOpenImmersion (b : Bool) :
    IsOpenImmersion (F b) := by
  unfold arithmeticOneFiniteInitialNodeChart
  infer_instance

/-- The full initial comparison commutes with its actual fifth and finite node maps. -/
@[reassoc] theorem arithmeticOneFiniteInitialIso_nodeChart (b : Bool) :
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
def arithmeticOneFiniteInitialPuncture (b : Bool) :
    branchTorus Q ⟶ arithmeticOneFiniteInitialObject hπ data H k m hj u hu b :=
  (A b).inv ≫ arithmeticFifthInitialPuncture hπ data H m 1 hj u hu b ≫ (I b).hom

/-- The puncture of the corrected initial open is the standard puncture of its new node. -/
@[reassoc] theorem arithmeticOneFiniteInitialPuncture_nodeChart (b : Bool) :
    arithmeticOneFiniteInitialPuncture hπ data H k m hj u hu b ≫ F b =
      leftBranchOpen Q ((arithmeticOneFiniteState hπ data H hj u hu k).initial m b) := by
  simp only [arithmeticOneFiniteInitialPuncture, Category.assoc,
    arithmeticOneFiniteInitialIso_nodeChart]
  rw [arithmeticFifthInitialPuncture_nodeChart_assoc]
  have h := arithmeticOneFiniteInitialNodeIso_puncture hπ data H k m hj u hu b true
  simp only [punctureOpen_true] at h
  rw [h, Iso.inv_hom_id_assoc]

local notation "T" => arithmeticOneFiniteTerminalFactor hπ data H hj u hu k m

/-- The common terminal is transported by the inverse of its full rebased factor. -/
def arithmeticOneFiniteTerminalIso :
    PolygonSmoothing.chart Q (arithmeticFifthShallowTerminalSmoothing hπ data H 1 hj u hu m) ≅
      PolygonSmoothing.chart Q ((arithmeticOneFiniteState hπ data H hj u hu k).terminal m) :=
  (Scheme.Spec.mapIso (T).toRingEquiv.toCommRingCatIso.op).symm

/-- Both inverse punctures come from the same full common terminal comparison. -/
@[reassoc] theorem arithmeticOneFiniteTerminalIso_puncture (b : Bool) :
    punctureOpen (arithmeticFifthShallowTerminalSmoothing hπ data H 1 hj u hu m) b ≫
        (arithmeticOneFiniteTerminalIso hπ data H k m hj u hu).hom =
      (punctureSpecIso
        (arithmeticOneFiniteTerminalPunctureEquiv hπ data H hj u hu k m b).symm).hom ≫
          punctureOpen ((arithmeticOneFiniteState hπ data H hj u hu k).terminal m) b := by
  apply punctureFactor_spec _ _ (T).symm
  apply punctureFactor_symm
  exact arithmeticOneFiniteTerminalFactor_puncture hπ data H hj u hu k m b

end FLT.Mazur.WeierstrassDividedDepth
