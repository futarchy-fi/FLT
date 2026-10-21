/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRetainedSelfReciprocalAddition
public import FLT.Mazur.WeierstrassDividedArithmeticAtlasPairPresentation

/-!
# Reciprocal coverage for the original arithmetic self-pairs

The initial and equal-creation-depth retained self-pairs keep both full
smooth arithmetic inputs. Reciprocal coverage requires no positive depth,
pre-middle bound, sum-depth range, or reduced coefficient quotient.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasObject globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
  retainedSelfFormulaCoordinates retainedSelfFormulaIndex
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j ≤ n) (a : Option (Fin j))
local notation "idx" => retainedSelfFormulaIndex j a
local notation "depth" => retainedSelfFormulaDepth j a
local notation "d" => data ⟨depth, Nat.lt_succ_of_le ((retainedSelfFormulaDepth_le j a).trans hj)⟩
local notation "f" => retainedSelfFormulaCoordinates hπ data j hj a
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "Q" => Quotient R π m
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "chart" => arithmeticTensorAtlasMap hπ data m j hj
local notation "s" => finiteGlobalArithmeticStructure hπ data j hj m
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q j hj idx
local notation "fa" => (O).ι ≫ chart idx ≫ s
local notation "coords" => tensorIntegralAtlasProjection hπ data Q j hj idx
local notation "P" => arithmeticAtlasPairPresentation hπ data m j hj idx idx
local notation "F" => retainedSelfFormulaInput hπ data j hj a
local notation "A" => DividedPairRing W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6

/-- Both whole original smooth arithmetic inputs supply the selected common divided coordinates. -/
def arithmeticSelfReciprocalFormulaInput : pullback fa fa ⟶ Spec (.of A) := P ≫ F

local notation "input" => arithmeticSelfReciprocalFormulaInput hπ data m j hj a
local notation "al" => dividedPairLeft W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6
local notation "ar" => dividedPairRight W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6

/-- The first input preserves all functions on the original arithmetic chart. -/
@[reassoc] theorem arithmeticSelfReciprocalFormulaInput_left :
    input ≫ Spec.map (CommRingCat.ofHom (al).toRingHom) =
      pullback.fst fa fa ≫ (O).ι ≫ coords ≫ f := by
  rw [arithmeticSelfReciprocalFormulaInput, Category.assoc, retainedSelfFormulaInput,
    atlasPairFormulaInput_left]
  dsimp only [arithmeticAtlasPairPresentation]
  rw [atlasPairPresentation_first_assoc]
  rfl

/-- The second input independently preserves the entire same arithmetic chart. -/
@[reassoc] theorem arithmeticSelfReciprocalFormulaInput_right :
    input ≫ Spec.map (CommRingCat.ofHom (ar).toRingHom) =
      pullback.snd fa fa ≫ (O).ι ≫ coords ≫ f := by
  rw [arithmeticSelfReciprocalFormulaInput, Category.assoc, retainedSelfFormulaInput,
    atlasPairFormulaInput_right]
  dsimp only [arithmeticAtlasPairPresentation]
  rw [atlasPairPresentation_second_assoc]
  rfl

local notation "V" => retainedSelfReciprocalOpen hπ data j hj a
local notation "add" => retainedSelfReciprocalAddition hπ data j hj a

/-- The reciprocal domain in the actual full arithmetic self-pair. -/
def arithmeticSelfReciprocalOpen : (pullback fa fa).Opens := P ⁻¹ᵁ V

local notation "D" => arithmeticSelfReciprocalOpen hπ data m j hj a

/-- The constructed output lies in the original final resolved smooth model. -/
def arithmeticSelfReciprocalAddition : (D).toScheme ⟶ (U).toScheme := (P ∣_ V) ≫ add

/-- The output retains exactly the first input's actual arithmetic coefficient point. -/
@[reassoc] theorem arithmeticSelfReciprocalAddition_structure :
    arithmeticSelfReciprocalAddition hπ data m j hj a ≫ t =
      (D).ι ≫ pullback.fst fa fa ≫ fa ≫ q := by
  rw [arithmeticSelfReciprocalAddition, Category.assoc,
    retainedSelfReciprocalAddition_structure, morphismRestrict_ι_assoc,
    finiteResolvedAtlasPairInput_fst_assoc, arithmeticAtlasPairPresentation_structure]
  simp only [Category.assoc, arithmeticSelfReciprocalOpen]

/-- The same output retains the second original arithmetic coefficient point. -/
@[reassoc] theorem arithmeticSelfReciprocalAddition_structure_snd :
    arithmeticSelfReciprocalAddition hπ data m j hj a ≫ t =
      (D).ι ≫ pullback.snd fa fa ≫ fa ≫ q := by
  rw [arithmeticSelfReciprocalAddition_structure, pullback.condition_assoc]

local notation "x₁" => al (x W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6)
local notation "y₁" => al (y W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6)
local notation "x₂" => ar (x W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6)
local notation "y₂" => ar (y W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6)
local notation "α" => algebraMap R A W.a₁

/-- Equal residue abscissae and different ordinates are covered at every arithmetic order. -/
theorem arithmeticSelfReciprocalOpen_mem (p : (pullback fa fa : Scheme))
    (hx : x₁ - x₂ ∈ (input p).asIdeal) (hy : y₁ - y₂ ∉ (input p).asIdeal) : p ∈ D :=
  retainedSelfReciprocalOpen_mem hπ data j hj a (P p) hx hy

/-- Opposite punctured equal-abscissa branches have outputs at every arithmetic order. -/
theorem arithmeticSelfReciprocalOpen_opposite_mem (hα : IsUnit W.a₁)
    (p : (pullback fa fa : Scheme)) (hx : x₁ - x₂ ∈ (input p).asIdeal)
    (hu : x₂ ∉ (input p).asIdeal)
    (hb : (y₁ ∈ (input p).asIdeal ∧ y₂ + α * x₂ ∈ (input p).asIdeal) ∨
      (y₁ + α * x₁ ∈ (input p).asIdeal ∧ y₂ ∈ (input p).asIdeal)) : p ∈ D :=
  retainedSelfReciprocalOpen_opposite_mem hπ data j hj a hα (P p) hx hu hb

end FLT.Mazur.WeierstrassDividedDepth
