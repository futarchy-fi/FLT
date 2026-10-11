/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialTensorPointAction
public import FLT.Mazur.WeierstrassDividedInitialPointActionPropagation

/-!
# The original horizontal residue action at every finite stage

Both concrete residue actions propagate through the full retained chart.
Every input still uses the original horizontal equation equivalence and
smooth point, and every output uses the actual finite tensor chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart WeierstrassGlobalModification
open WeierstrassModificationReesCoordinates
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (hstart : 0 < start) (hk : 2 * start < depth)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "e" => finiteGlobalInitialIso hπ data
local notation "p" => smoothHorizontalPoint W (π ^ start)
local notation "ψ" => smoothHorizontalInput W (π ^ start)
local notation "j" => originalFractionCoverMap W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
  (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) (pow_ne_zero start hπ) (some 1)
local notation "b" => Spec.map (CommRingCat.ofHom ψ) ≫ j
local notation "base" => finiteGlobalStructure hπ data 0 (Nat.zero_le n)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "g" => globalInitialTensorChart hπ data K 0 (Nat.zero_le n)
local notation "e₁" => smoothHorizontalFirstResidue D start hstart hk hπ
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
  (Data.factor3 d) (Data.factor4 d) (Data.factor6 d)
local notation "e₂" => smoothHorizontalSecondResidue D start hstart hk hπ
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
  (Data.factor3 d) (Data.factor4 d) (Data.factor6 d)

local notation "A" => WeierstrassModificationX.Coordinate W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "E" => WeierstrassModificationX.horizontalReesChartEquiv W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
  (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) (pow_ne_zero start hπ)

omit hstart hk in
/-- The original horizontal input as a point of the actual integral equation chart. -/
def initialHorizontalEquationInput
    (f : SmoothHorizontalProductRing W (π ^ start) →+* SmoothHorizontalResidueRing D) :
    Spec (.of (SmoothHorizontalResidueRing D)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (f.comp ((ψ).comp (E).toAlgHom.toRingHom)))

omit hstart hk in
/-- The integral equation input is exactly the previously transported whole-model input. -/
theorem initialHorizontalEquationInput_initial
    (f : SmoothHorizontalProductRing W (π ^ start) →+* SmoothHorizontalResidueRing D) :
    initialHorizontalEquationInput hπ data D f ≫
        globalInitialChart hπ data 0 (Nat.zero_le n) =
      (Spec.map (CommRingCat.ofHom f) ≫ b) ≫ (e).inv := by
  apply (cancel_mono (e).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [globalInitialChart, Category.assoc, finiteInitialChart_globalInitialIso]
  rw [initialHorizontalEquationInput, CommRingCat.ofHom_comp, Spec.map_comp,
    CommRingCat.ofHom_comp, Spec.map_comp]
  simp only [Category.assoc, originalHorizontalFractionCoverMap_spec]

omit hstart hk in
/-- Each original residue input has the required integral coefficient morphism. -/
theorem initialHorizontalEquationInput_structure
    (f : SmoothHorizontalProductRing W (π ^ start) →+* SmoothHorizontalResidueRing D) :
    (Spec.map (CommRingCat.ofHom f) ≫ p) ≫ integralSmoothStructure W =
      initialHorizontalEquationInput hπ data D f ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  have h := initialHorizontalInput_structure hπ data D f
  rw [← initialHorizontalEquationInput_initial hπ data D f] at h
  simpa only [Category.assoc, globalInitialChart_structure] using h

/-- The first concrete tensor action is the actual action at every finite stage. -/
theorem finiteHorizontalFirstTensorAction_point (j' : ℕ) (hj' : j' ≤ n) :
    finiteGlobalPointAction hπ data j' hj'
      (Spec.map (CommRingCat.ofHom (e₁).toRingHom) ≫ p)
      (initialHorizontalEquationInput hπ data D (e₁).toRingHom ≫
        globalInitialChart hπ data j' hj')
      (globalInitialChart_input_condition hπ data _ _
        (initialHorizontalEquationInput_structure hπ data D (e₁).toRingHom) j' hj') =
      Spec.map (CommRingCat.ofHom
        (smoothHorizontalFirstTensorAction D d hstart hk hπ).toRingHom) ≫
        globalInitialTensorChart hπ data K j' hj' ≫
          pullback.snd q (finiteGlobalStructure hπ data j' hj') := by
  rw [globalInitialTensorChart_projection, ← Category.assoc]
  apply globalInitialChart_pointAction_propagate hπ data _ _ _
    (initialHorizontalEquationInput_structure hπ data D (e₁).toRingHom)
  have h := initialHorizontalFirstTensorAction_point hπ data D hstart hk
  rw [globalInitialTensorChart_projection] at h
  simpa only [initialHorizontalEquationInput_initial, Category.assoc] using h.symm

/-- The second concrete tensor action is the actual action at every finite stage. -/
theorem finiteHorizontalSecondTensorAction_point (j' : ℕ) (hj' : j' ≤ n) :
    finiteGlobalPointAction hπ data j' hj'
      (Spec.map (CommRingCat.ofHom (e₂).toRingHom) ≫ p)
      (initialHorizontalEquationInput hπ data D (e₂).toRingHom ≫
        globalInitialChart hπ data j' hj')
      (globalInitialChart_input_condition hπ data _ _
        (initialHorizontalEquationInput_structure hπ data D (e₂).toRingHom) j' hj') =
      Spec.map (CommRingCat.ofHom
        (smoothHorizontalSecondTensorAction D d hstart hk hπ).toRingHom) ≫
        globalInitialTensorChart hπ data K j' hj' ≫
          pullback.snd q (finiteGlobalStructure hπ data j' hj') := by
  rw [globalInitialTensorChart_projection, ← Category.assoc]
  apply globalInitialChart_pointAction_propagate hπ data _ _ _
    (initialHorizontalEquationInput_structure hπ data D (e₂).toRingHom)
  have h := initialHorizontalSecondTensorAction_point hπ data D hstart hk
  rw [globalInitialTensorChart_projection] at h
  simpa only [initialHorizontalEquationInput_initial, Category.assoc] using h.symm

end FLT.Mazur.WeierstrassDividedDepth
