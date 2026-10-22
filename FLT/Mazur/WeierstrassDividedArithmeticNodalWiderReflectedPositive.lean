/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticOlderOwnInput
public import FLT.Mazur.WeierstrassDividedOlderNodalWiderReflectedAddition

/-!
# Positive wider reflected-depth retained outputs at every arithmetic order

Pull back the constructed positive output along the complete arithmetic pair
presentation. The quotient itself supplies closed-fiber support, and both
coefficient identities hold on the whole domain, including nilpotent orders.
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
  retainedOlderLowerCoordinates retainedOlderFormulaIndex
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n depth : ℕ} (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j ≤ n) (k l : ℕ) (hk : k < j) (hl : l < j)
local notation "hπ" => node.uniformizer_ne_zero
local notation "a" => retainedOlderFormulaIndex j k hk
local notation "b" => retainedOlderFormulaIndex j l hl
local notation "d" => data ⟨k, Nat.lt_succ_of_le (hk.le.trans hj)⟩
local notation "e" => data ⟨l, Nat.lt_succ_of_le (hl.le.trans hj)⟩
local notation "f" => retainedOlderLowerCoordinates hπ data j hj k hk k le_rfl
local notation "g" => retainedOlderLowerCoordinates hπ data j hj l hl l le_rfl
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "Q" => Quotient R π m
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "chart" => arithmeticTensorAtlasMap hπ data m j hj
local notation "s" => finiteGlobalArithmeticStructure hπ data j hj m
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q j hj
local notation "fa" => (O a).ι ≫ chart a ≫ s
local notation "fb" => (O b).ι ≫ chart b ≫ s
local notation "coords" => tensorIntegralAtlasProjection hπ data Q j hj
local notation "P" => arithmeticAtlasPairPresentation hπ data m j hj a b
local notation "input" => arithmeticOlderOwnFormulaInput hπ data m j hj k l hk hl
variable (hkl : k ≤ l) (hdepth : k + 2 * l ≤ depth) (hnear : depth ≤ 2 * (k + l))
  (hsum : depth - k - l ≤ j)
local notation "V" => olderNodalWiderReflectedOpen node data j hj k l hk hl hkl hdepth hnear hsum
local notation "add" => olderNodalWiderReflectedAddition node data j hj k l hk hl
      hkl hdepth hnear hsum

/-- Pull the actual wider reflected-depth domain back to the complete arithmetic retained pair. -/
def arithmeticOlderNodalWiderReflectedPositiveOpen : (pullback fa fb).Opens := P ⁻¹ᵁ V

local notation "D" => arithmeticOlderNodalWiderReflectedPositiveOpen node data m j hj k l hk hl
  hkl hdepth hnear hsum

/-- Construct a smooth output from the same full arithmetic inputs at every order. -/
def arithmeticOlderNodalWiderReflectedPositiveAddition : (D).toScheme ⟶ (U).toScheme :=
  (P ∣_ V) ≫ add

/-- The output has precisely the original first arithmetic coefficient point. -/
@[reassoc] theorem arithmeticOlderNodalWiderReflectedPositiveAddition_structure :
    arithmeticOlderNodalWiderReflectedPositiveAddition node data m j hj k l hk hl
      hkl hdepth hnear hsum ≫
      t =
      (D).ι ≫ pullback.fst fa fb ≫ fa ≫ q := by
  rw [arithmeticOlderNodalWiderReflectedPositiveAddition, Category.assoc,
    olderNodalWiderReflectedAddition_structure]
  dsimp only [olderNodalWiderReflectedInput]
  simp only [Category.assoc]
  rw [morphismRestrict_ι_assoc,
    finiteResolvedAtlasPairInput_fst_assoc, arithmeticAtlasPairPresentation_structure]
  simp only [Category.assoc, arithmeticOlderNodalWiderReflectedPositiveOpen]

/-- The same output has the original second arithmetic coefficient point. -/
@[reassoc] theorem arithmeticOlderNodalWiderReflectedPositiveAddition_structure_snd :
    arithmeticOlderNodalWiderReflectedPositiveAddition node data m j hj k l hk hl
      hkl hdepth hnear hsum ≫
      t =
      (D).ι ≫ pullback.snd fa fb ≫ fb ≫ q := by
  rw [arithmeticOlderNodalWiderReflectedPositiveAddition_structure, pullback.condition_assoc]

/-- The constructed output lifts to the actual arithmetic base change of the smooth model. -/
def arithmeticOlderNodalWiderReflectedPositiveQuotientOutput : (D).toScheme ⟶ pullback q t :=
  pullback.lift ((D).ι ≫ pullback.fst fa fb ≫ fa)
    (arithmeticOlderNodalWiderReflectedPositiveAddition node data m j hj k l hk hl
      hkl hdepth hnear hsum)
    (by simpa only [Category.assoc] using
      (arithmeticOlderNodalWiderReflectedPositiveAddition_structure node data m j hj k l hk hl
        hkl hdepth hnear hsum).symm)

/-- The arithmetic output has the exact original quotient coefficient morphism. -/
@[reassoc] theorem arithmeticOlderNodalWiderReflectedPositiveQuotientOutput_base :
    arithmeticOlderNodalWiderReflectedPositiveQuotientOutput node data m j hj k l hk hl
        hkl hdepth hnear hsum ≫ pullback.fst q t = (D).ι ≫ pullback.fst fa fb ≫ fa := by
  simp only [arithmeticOlderNodalWiderReflectedPositiveQuotientOutput, pullback.lift_fst]

/-- Projection recovers the entire constructed integral smooth output. -/
@[reassoc] theorem arithmeticOlderNodalWiderReflectedPositiveQuotientOutput_integral :
    arithmeticOlderNodalWiderReflectedPositiveQuotientOutput node data m j hj k l hk hl
        hkl hdepth hnear hsum ≫ pullback.snd q t =
      arithmeticOlderNodalWiderReflectedPositiveAddition node data m j hj k l hk hl
      hkl hdepth hnear hsum := by
  simp only [arithmeticOlderNodalWiderReflectedPositiveQuotientOutput, pullback.lift_snd]

local notation "al" => unequalPairLeft d e
local notation "ar" => unequalPairRight d e
local notation "x₁" => al (x W (π ^ (0 + k)) (d).b3 (d).b4 (d).b6)
local notation "y₁" => al (y W (π ^ (0 + k)) (d).b3 (d).b4 (d).b6)
local notation "x₂" => ar (x W (π ^ (0 + l)) (e).b3 (e).b4 (e).b6)
local notation "y₂" => ar (y W (π ^ (0 + l)) (e).b3 (e).b4 (e).b6)

/-- Positive arithmetic branches are covered, throughout the strict wider range. -/
theorem arithmeticOlderNodalWiderReflectedPositiveOpen_mem (hk0 : 0 < k) (hlt : k < l)
    (hm : depth < 2 * (k + l)) (p : (pullback fa fb : Scheme))
    (hx : x₁ ∉ (input p).asIdeal) (hu : x₂ ∉ (input p).asIdeal)
    (hy : y₁ ∈ (input p).asIdeal) (hv : y₂ ∈ (input p).asIdeal) : p ∈ D :=
  olderNodalWiderReflectedOpen_positive_mem node data j hj k l hk hl hkl hdepth hnear hsum
    hk0 hlt hm (P p)
    (arithmeticOlderOwnFormulaInput_parameter_mem hπ data m j hj k l hk hl p) hx hu hy hv

end FLT.Mazur.WeierstrassDividedDepth
