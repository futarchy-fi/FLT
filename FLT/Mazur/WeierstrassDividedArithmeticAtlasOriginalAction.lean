/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAtlasOriginalAction
public import FLT.Mazur.WeierstrassDividedArithmeticAtlasRelativeSmooth

/-!
# Arithmetic atlas action outputs with full original coefficients

Whenever the first integral chart contracts by an open immersion, its entire
smooth arithmetic pair has an output over the original quotient. The second
chart is unrestricted, and reversal retains both whole input morphisms.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart PolygonArithmeticStages
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasObject globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
  globalTensorAtlasObject arithmeticTensorAtlasMap tensorIntegralAtlasProjection
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (m j : ℕ) (hj : j ≤ n) (a b : Fin (j + 3))
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "c" => finiteGlobalContraction hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "Q" => Quotient R π m
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "chart" => arithmeticTensorAtlasMap hπ data m j hj
local notation "s" => finiteGlobalArithmeticStructure hπ data j hj m
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q j hj
local notation "fa" => (O a).ι ≫ chart a ≫ s
local notation "fb" => (O b).ι ≫ chart b ≫ s
local notation "P" => arithmeticAtlasPairPresentation hπ data m j hj a b
variable [IsOpenImmersion (globalIntegralAtlasMap hπ data j hj a ≫
  finiteGlobalContraction hπ data j hj)]

/-- Every full arithmetic pair with an unchanged first chart has a resolved action output. -/
def arithmeticAtlasOriginalActionOutput : pullback fa fb ⟶ (U).toScheme :=
  P ≫ atlasOriginalActionOutput hπ data j hj a b

local notation "out" => arithmeticAtlasOriginalActionOutput hπ data m j hj a b

/-- The output retains the entire first arithmetic coefficient morphism. -/
@[reassoc] theorem arithmeticAtlasOriginalActionOutput_structure :
    out ≫ t = pullback.fst fa fb ≫ fa ≫ q := by
  rw [arithmeticAtlasOriginalActionOutput, Category.assoc,
    atlasOriginalActionOutput_structure, arithmeticAtlasPairPresentation_structure]

/-- The second input gives the same full coefficient morphism. -/
@[reassoc] theorem arithmeticAtlasOriginalActionOutput_structure_snd :
    out ≫ t = pullback.snd fa fb ≫ fb ≫ q := by
  rw [arithmeticAtlasOriginalActionOutput_structure, pullback.condition_assoc]

/-- Lift the whole output to the unchanged quotient, without reducing its nilpotents. -/
def arithmeticAtlasOriginalActionQuotientOutput : pullback fa fb ⟶ pullback q t :=
  pullback.lift (pullback.fst fa fb ≫ fa) out (by
    simpa only [Category.assoc] using
      (arithmeticAtlasOriginalActionOutput_structure hπ data m j hj a b).symm)

local notation "output" => arithmeticAtlasOriginalActionQuotientOutput hπ data m j hj a b

/-- Quotient projection retains the first original arithmetic structure map. -/
@[reassoc] theorem arithmeticAtlasOriginalActionQuotientOutput_base :
    output ≫ pullback.fst q t = pullback.fst fa fb ≫ fa := pullback.lift_fst _ _ _

/-- Integral projection is precisely the constructed whole resolved output. -/
@[reassoc] theorem arithmeticAtlasOriginalActionQuotientOutput_integral :
    output ≫ pullback.snd q t = out := pullback.lift_snd _ _ _

/-- Reverse the original input order while retaining the same complete quotient output. -/
def arithmeticAtlasOriginalActionReversedOutput : pullback fb fa ⟶ pullback q t :=
  (pullbackSymmetry fb fa).hom ≫ output

/-- Reversal retains the new first coefficient morphism. -/
@[reassoc] theorem arithmeticAtlasOriginalActionReversedOutput_base :
    arithmeticAtlasOriginalActionReversedOutput hπ data m j hj a b ≫ pullback.fst q t =
      pullback.fst fb fa ≫ fb := by
  rw [arithmeticAtlasOriginalActionReversedOutput, Category.assoc,
    arithmeticAtlasOriginalActionQuotientOutput_base,
    pullbackSymmetry_hom_comp_fst_assoc, pullback.condition]

/-- Reversal also retains the new second coefficient morphism. -/
@[reassoc] theorem arithmeticAtlasOriginalActionReversedOutput_base_snd :
    arithmeticAtlasOriginalActionReversedOutput hπ data m j hj a b ≫ pullback.fst q t =
      pullback.snd fb fa ≫ fa := by
  rw [arithmeticAtlasOriginalActionReversedOutput_base, pullback.condition]

/-- Swapping back recovers the entire original quotient-valued morphism. -/
@[reassoc] theorem arithmeticAtlasOriginalActionReversedOutput_swap :
    (pullbackSymmetry fa fb).hom ≫
      arithmeticAtlasOriginalActionReversedOutput hπ data m j hj a b = output := by
  rw [arithmeticAtlasOriginalActionReversedOutput,
    ← Category.assoc (pullbackSymmetry fa fb).hom (pullbackSymmetry fb fa).hom]
  have he : (pullbackSymmetry fa fb).hom ≫ (pullbackSymmetry fb fa).hom = 𝟙 _ := by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, pullbackSymmetry_hom_comp_fst,
        pullbackSymmetry_hom_comp_snd, Category.id_comp]
  rw [he, Category.id_comp]

local instance arithmeticAtlasOriginalAction_structure :
    LocallyOfFinitePresentation s := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

local notation "f" => chart a ≫ s
local notation "g" => chart b ≫ s

/-- Relatively smooth full inputs reach this output with both original coordinates intact. -/
theorem arithmeticAtlasOriginalAction_target (p : (pullback f g : Scheme))
    (hs : chart a (pullback.fst f g p) ∈ (s).smoothLocus)
    (ht : chart b (pullback.snd f g p) ∈ (s).smoothLocus) :
    ∃ z : (pullback fa fb : Scheme),
      (O a).ι (pullback.fst fa fb z) = pullback.fst f g p ∧
      (O b).ι (pullback.snd fa fb z) = pullback.snd f g p ∧
      pullback.fst q t (output z) = fa (pullback.fst fa fb z) := by
  obtain ⟨z, hz, he⟩ := arithmeticAtlasRelativePair_exists hπ data m j hj a b p hs ht
  exact ⟨z, hz, he, congrArg (fun morphism => morphism z)
    (arithmeticAtlasOriginalActionQuotientOutput_base hπ data m j hj a b)⟩

end FLT.Mazur.WeierstrassDividedDepth
