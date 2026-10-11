/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedHorizontalFinitePointAction
public import FLT.Mazur.WeierstrassSmoothHorizontalTensorInput
public import FLT.Mazur.WeierstrassSmoothHorizontalResiduePoint
public import FLT.Mazur.WeierstrassDividedGlobalCoefficientOverAction

/-!
# Actual coefficient actions on both original horizontal conic inputs

Both finite tensor actions are the original coefficient action, on the
original smooth residue point and the independently constructed conic inputs.
The comparison holds at every finite stage and retains both pullback projections.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open MonoidalCategory CartesianMonoidalCategory
open scoped TensorProduct MonObj
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
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "e₁" => smoothHorizontalFirstResidue D start hstart hk hπ
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
  (Data.factor3 d) (Data.factor4 d) (Data.factor6 d)
local notation "e₂" => smoothHorizontalSecondResidue D start hstart hk hπ
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
  (Data.factor3 d) (Data.factor4 d) (Data.factor6 d)

local notation "A" => WeierstrassModificationX.Coordinate W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "C" => SmoothHorizontalResidueRing D
local notation "V" => W.map (algebraMap R K)
local notation "a" => smoothHorizontalResiduePoint D (by omega)
local notation "c" => Spec.map (CommRingCat.ofHom (algebraMap K C))
variable (j' : ℕ) (hj' : j' ≤ n)
local notation "g'" => globalInitialTensorChart hπ data K j' hj'
local notation "base'" => finiteGlobalStructure hπ data j' hj'
local notation "fst'" => pullback.fst q base'
local notation "snd'" => pullback.snd q base'

omit hstart hk in
/-- Any algebra-valued point in the original tensor chart preserves residue coefficients. -/
theorem horizontalTensorPoint_structure (f : K ⊗[R] A →ₐ[K] C) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ g' ≫ fst' = c := by
  rw [globalInitialTensorChart_structure, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext f.commutes

omit hstart hk in
/-- A tensor-chart algebra point as a morphism over the residue coefficient scheme. -/
def horizontalTensorOverPoint (f : K ⊗[R] A →ₐ[K] C) : Over.mk c ⟶ Over.mk fst' :=
  Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ g') (by
    change (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ g') ≫ fst' = c
    rw [Category.assoc]
    exact horizontalTensorPoint_structure hπ data D j' hj' f)

/-- The first original conic tensor input projects to the retained integral input. -/
theorem finiteHorizontalFirstTensorInput_projection :
    Spec.map (CommRingCat.ofHom
        (smoothHorizontalFirstTensorInput D d hstart hk).toRingHom) ≫ g' ≫ snd' =
      initialHorizontalEquationInput hπ data D (e₁).toRingHom ≫
        globalInitialChart hπ data j' hj' := by
  rw [globalInitialTensorChart_integralProjection, ← Category.assoc,
    smoothHorizontalFirstTensorInput_projection D d hstart hk hπ]
  rfl

/-- The first original conic and the actual smooth parameter share their residue base. -/
theorem finiteHorizontalFirstCoefficientInput_condition :
    a ≫ integralSmoothStructure V =
      (Spec.map (CommRingCat.ofHom
        (smoothHorizontalFirstTensorInput D d hstart hk).toRingHom) ≫ g') ≫ fst' := by
  rw [Category.assoc, horizontalTensorPoint_structure,
    smoothHorizontalResiduePoint_structure]

/-- The first tensor action is the actual coefficient action at every finite stage. -/
theorem finiteHorizontalFirstTensorAction_coefficient :
    Spec.map (CommRingCat.ofHom
        (smoothHorizontalFirstTensorAction D d hstart hk hπ).toRingHom) ≫ g' =
      finiteGlobalCoefficientPointAction hπ data j' hj' K a
        (Spec.map (CommRingCat.ofHom
          (smoothHorizontalFirstTensorInput D d hstart hk).toRingHom) ≫ g')
        (finiteHorizontalFirstCoefficientInput_condition hπ data D hstart hk j' hj') := by
  apply pullback.hom_ext
  · simp only [Category.assoc, horizontalTensorPoint_structure,
      finiteGlobalCoefficientPointAction_structure, smoothHorizontalResiduePoint_structure]
  · simp only [finiteGlobalCoefficientPointAction_projection, Category.assoc,
      finiteHorizontalFirstTensorInput_projection,
      ← smoothHorizontalFirstResiduePoint_original D d hstart hk hπ]
    exact (finiteHorizontalFirstTensorAction_point hπ data D hstart hk j' hj').symm

/-- The second original conic tensor input projects to the retained integral input. -/
theorem finiteHorizontalSecondTensorInput_projection :
    Spec.map (CommRingCat.ofHom
        (smoothHorizontalSecondTensorInput D d hstart hk).toRingHom) ≫ g' ≫ snd' =
      initialHorizontalEquationInput hπ data D (e₂).toRingHom ≫
        globalInitialChart hπ data j' hj' := by
  rw [globalInitialTensorChart_integralProjection, ← Category.assoc,
    smoothHorizontalSecondTensorInput_projection D d hstart hk hπ]
  rfl

/-- The second original conic and the actual smooth parameter share their residue base. -/
theorem finiteHorizontalSecondCoefficientInput_condition :
    a ≫ integralSmoothStructure V =
      (Spec.map (CommRingCat.ofHom
        (smoothHorizontalSecondTensorInput D d hstart hk).toRingHom) ≫ g') ≫ fst' := by
  rw [Category.assoc, horizontalTensorPoint_structure,
    smoothHorizontalResiduePoint_structure]

/-- The second tensor action is the actual coefficient action at every finite stage. -/
theorem finiteHorizontalSecondTensorAction_coefficient :
    Spec.map (CommRingCat.ofHom
        (smoothHorizontalSecondTensorAction D d hstart hk hπ).toRingHom) ≫ g' =
      finiteGlobalCoefficientPointAction hπ data j' hj' K a
        (Spec.map (CommRingCat.ofHom
          (smoothHorizontalSecondTensorInput D d hstart hk).toRingHom) ≫ g')
        (finiteHorizontalSecondCoefficientInput_condition hπ data D hstart hk j' hj') := by
  apply pullback.hom_ext
  · simp only [Category.assoc, horizontalTensorPoint_structure,
      finiteGlobalCoefficientPointAction_structure, smoothHorizontalResiduePoint_structure]
  · simp only [finiteGlobalCoefficientPointAction_projection, Category.assoc,
      finiteHorizontalSecondTensorInput_projection,
      ← smoothHorizontalSecondResiduePoint_original D d hstart hk hπ]
    exact (finiteHorizontalSecondTensorAction_point hπ data D hstart hk j' hj').symm

/-- The actual relative action evaluates to the first tensor output on the original inputs. -/
theorem finiteHorizontalFirstTensorAction_over :
    lift (Over.homMk (U := Over.mk c) («V» := (integralSmoothGroup V).X) a
      (smoothHorizontalResiduePoint_structure D (by omega)))
      (horizontalTensorOverPoint hπ data D j' hj'
        (smoothHorizontalFirstTensorInput D d hstart hk)) ≫
      finiteGlobalCoefficientOverAction hπ data j' hj' K =
        horizontalTensorOverPoint hπ data D j' hj'
          (smoothHorizontalFirstTensorAction D d hstart hk hπ) := by
  rw [finiteGlobalCoefficientOverAction_points]
  apply Over.OverMorphism.ext
  exact (finiteHorizontalFirstTensorAction_coefficient hπ data D hstart hk j' hj').symm

/-- The actual relative action evaluates to the second tensor output on the original inputs. -/
theorem finiteHorizontalSecondTensorAction_over :
    lift (Over.homMk (U := Over.mk c) («V» := (integralSmoothGroup V).X) a
      (smoothHorizontalResiduePoint_structure D (by omega)))
      (horizontalTensorOverPoint hπ data D j' hj'
        (smoothHorizontalSecondTensorInput D d hstart hk)) ≫
      finiteGlobalCoefficientOverAction hπ data j' hj' K =
        horizontalTensorOverPoint hπ data D j' hj'
          (smoothHorizontalSecondTensorAction D d hstart hk hπ) := by
  rw [finiteGlobalCoefficientOverAction_points]
  apply Over.OverMorphism.ext
  exact (finiteHorizontalSecondTensorAction_coefficient hπ data D hstart hk j' hj').symm

end FLT.Mazur.WeierstrassDividedDepth
