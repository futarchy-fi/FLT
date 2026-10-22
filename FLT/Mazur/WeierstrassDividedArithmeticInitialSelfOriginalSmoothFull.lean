/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticSelfOriginalSmoothAddition
public import FLT.Mazur.WeierstrassDividedInitialFormulaPuncture

/-!
# Complete arithmetic initial self-pair output at every final stage

The initial horizontal coordinate is a unit, so the original smooth law
covers the entire initial self-pair, including final stage zero and node depth one.
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
  retainedSelfFormulaCoordinates arithmeticTensorAtlasMap
  globalTensorAtlasObject tensorIntegralAtlasProjection
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {nodeDepth n : ℕ}
  (node : SplitNodeDepth W π nodeDepth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j ≤ n)
local notation "hπ" => node.uniformizer_ne_zero
local notation "idx" => (Fin.succ ⟨j + 1, Nat.lt_succ_self (j + 1)⟩ : Fin (j + 3))
local notation "depth" => 0
local notation "d" => data ⟨depth,
  Nat.lt_succ_of_le ((retainedSelfFormulaDepth_le j none).trans hj)⟩
local notation "f" => retainedSelfFormulaCoordinates hπ data j hj none
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
local notation "F" => retainedSelfFormulaInput hπ data j hj none
local notation "A" => DividedPairRing W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6

local notation "input" => arithmeticSelfReciprocalFormulaInput hπ data m j hj none
local notation "al" => dividedPairLeft W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6
local notation "ar" => dividedPairRight W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6

local notation "x₁" => al (x W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6)
local notation "x₂" => ar (x W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6)
local notation "D" => arithmeticSelfOriginalSmoothOpen node data m j hj none

/-- Both original initial inputs have a unit horizontal coordinate. -/
theorem arithmeticInitialSelfFormulaInput_punctured (p : (pullback fa fa : Scheme)) :
    x₁ ∉ (input p).asIdeal ∧ x₂ ∉ (input p).asIdeal := by
  constructor
  · have he := congrArg (fun morphism => morphism p)
      (arithmeticSelfReciprocalFormulaInput_left hπ data m j hj none)
    change PrimeSpectrum.comap (al).toRingHom (input p) =
      f (coords ((O).ι (pullback.fst fa fa p))) at he
    change x W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6 ∉
      (PrimeSpectrum.comap (al).toRingHom (input p)).asIdeal
    rw [he]
    simp only [retainedSelfFormulaCoordinates]
    exact retainedInitialFormulaCoordinates_punctured data j hj
      (coords ((O).ι (pullback.fst fa fa p)))
  · have he := congrArg (fun morphism => morphism p)
      (arithmeticSelfReciprocalFormulaInput_right hπ data m j hj none)
    change PrimeSpectrum.comap (ar).toRingHom (input p) =
      f (coords ((O).ι (pullback.snd fa fa p))) at he
    change x W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6 ∉
      (PrimeSpectrum.comap (ar).toRingHom (input p)).asIdeal
    rw [he]
    simp only [retainedSelfFormulaCoordinates]
    exact retainedInitialFormulaCoordinates_punctured data j hj
      (coords ((O).ι (pullback.snd fa fa p)))

/-- At positive node depth the original smooth law covers the whole initial self-pair. -/
theorem arithmeticInitialSelfOriginalSmoothOpen_eq_top (hd : 0 < nodeDepth) : D = ⊤ := by
  apply top_unique
  intro p _
  obtain ⟨hx, hy⟩ := arithmeticInitialSelfFormulaInput_punctured node data m j hj p
  exact arithmeticSelfOriginalSmoothOpen_zero_mem node data m j hj none rfl hd p hx hy

variable (hd : 0 < nodeDepth)

include hd in
/-- The complete initial self-domain has invertible inclusion. -/
theorem arithmeticInitialSelfOriginalSmooth_inclusion_isIso : IsIso (D).ι := by
  rw [arithmeticInitialSelfOriginalSmoothOpen_eq_top node data m j hj hd]
  exact (pullback fa fa).topIso.isIso_hom

/-- The entire initial self-pair has a constructed output in the original smooth model. -/
def arithmeticInitialSelfOriginalSmoothOutput : pullback fa fa ⟶ (U).toScheme := by
  let _ := arithmeticInitialSelfOriginalSmooth_inclusion_isIso node data m j hj hd
  exact inv (D).ι ≫ arithmeticSelfOriginalSmoothAddition node data m j hj none

local notation "out" => arithmeticInitialSelfOriginalSmoothOutput node data m j hj hd

/-- Restriction recovers the complete original smooth addition morphism. -/
@[reassoc] theorem arithmeticInitialSelfOriginalSmoothOutput_restrict :
    (D).ι ≫ out = arithmeticSelfOriginalSmoothAddition node data m j hj none := by
  let _ := arithmeticInitialSelfOriginalSmooth_inclusion_isIso node data m j hj hd
  rw [arithmeticInitialSelfOriginalSmoothOutput, IsIso.hom_inv_id_assoc]

/-- The full output retains the original coefficient morphism. -/
@[reassoc] theorem arithmeticInitialSelfOriginalSmoothOutput_structure :
    out ≫ t = pullback.fst fa fa ≫ fa ≫ q := by
  let _ := arithmeticInitialSelfOriginalSmooth_inclusion_isIso node data m j hj hd
  rw [arithmeticInitialSelfOriginalSmoothOutput, Category.assoc,
    arithmeticSelfOriginalSmoothAddition_structure, IsIso.inv_hom_id_assoc]
  rfl

/-- The full output is defined over the original quotient, including nilpotents. -/
def arithmeticInitialSelfOriginalSmoothQuotientOutput : pullback fa fa ⟶ pullback q t :=
  pullback.lift (pullback.fst fa fa ≫ fa) out (by
    simpa only [Category.assoc] using
      (arithmeticInitialSelfOriginalSmoothOutput_structure node data m j hj hd).symm)

/-- The first quotient projection retains the first original coefficient morphism. -/
@[reassoc] theorem arithmeticInitialSelfOriginalSmoothQuotientOutput_base :
    arithmeticInitialSelfOriginalSmoothQuotientOutput node data m j hj hd ≫
      pullback.fst q t = pullback.fst fa fa ≫ fa := pullback.lift_fst _ _ _

/-- The second original input gives the same complete coefficient morphism. -/
@[reassoc] theorem arithmeticInitialSelfOriginalSmoothQuotientOutput_base_snd :
    arithmeticInitialSelfOriginalSmoothQuotientOutput node data m j hj hd ≫
      pullback.fst q t = pullback.snd fa fa ≫ fa := by
  rw [arithmeticInitialSelfOriginalSmoothQuotientOutput_base, pullback.condition]

end FLT.Mazur.WeierstrassDividedDepth
