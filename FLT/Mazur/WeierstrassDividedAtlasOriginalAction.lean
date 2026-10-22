/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalSmoothAtlas
public import FLT.Mazur.WeierstrassDividedResolvedSmoothAction

/-!
# Whole atlas pairs with an unchanged original first chart

An atlas chart whose cubic contraction is an open immersion maps its entire
relative smooth locus to the original smooth curve. Its action then gives a
resolved output for every smooth second chart, without depth restrictions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasObject globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j ≤ n) (a : Fin (j + 3))
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "c" => finiteGlobalContraction hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "atlas" => globalIntegralAtlasMap hπ data j hj
local notation "O" => globalSmoothAtlasOpen hπ data j hj
local notation "smooth" => globalSmoothAtlasMap hπ data j hj
variable [IsOpenImmersion (globalIntegralAtlasMap hπ data j hj a ≫
  finiteGlobalContraction hπ data j hj)]

/-- An unchanged chart detects precisely the original smooth open. -/
theorem globalSmoothAtlasOpen_original_preimage :
    O a = (atlas a ≫ c) ⁻¹ᵁ integralSmoothOpen W := by
  unfold globalSmoothAtlasOpen
  change atlas a ⁻¹ᵁ (base).smoothLocus =
    (atlas a ≫ c) ⁻¹ᵁ (integralCurveStructure W).smoothLocus
  rw [Scheme.Hom.preimage_smoothLocus_eq, Scheme.Hom.preimage_smoothLocus_eq]
  congr 1
  simp only [finiteGlobalStructure, Category.assoc]

/-- The complete smooth chart contracts into the original smooth curve. -/
def globalSmoothAtlasOriginalInput : (O a).toScheme ⟶ (integralSmoothOpen W).toScheme :=
  IsOpenImmersion.lift (integralSmoothOpen W).ι ((O a).ι ≫ atlas a ≫ c) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact (globalSmoothAtlasOpen_original_preimage hπ data j hj a).le x.property)

local notation "original" => globalSmoothAtlasOriginalInput hπ data j hj a

/-- The smooth contraction retains every function on the original cubic. -/
@[reassoc] theorem globalSmoothAtlasOriginalInput_inclusion :
    original ≫ (integralSmoothOpen W).ι = (O a).ι ≫ atlas a ≫ c :=
  IsOpenImmersion.lift_fac _ _ _

/-- Its structure map is the unchanged full smooth atlas structure map. -/
@[reassoc] theorem globalSmoothAtlasOriginalInput_structure :
    original ≫ integralSmoothStructure W = smooth a ≫ t := by
  change original ≫ (integralSmoothOpen W).ι ≫ integralCurveStructure W = _
  rw [globalSmoothAtlasOriginalInput_inclusion_assoc,
    globalSmoothAtlasMap_inclusion_assoc]
  simp only [finiteGlobalStructure]

variable (b : Fin (j + 3))
local notation "fa" => smooth a ≫ t
local notation "fb" => smooth b ≫ t

/-- Act with the original first chart on every point of the full second smooth chart. -/
def atlasOriginalActionOutput : pullback fa fb ⟶ (U).toScheme :=
  finiteGlobalSmoothPointAction hπ data j hj
    (pullback.fst fa fb ≫ original) (pullback.snd fa fb ≫ smooth b) (by
      rw [Category.assoc, globalSmoothAtlasOriginalInput_structure]
      simpa only [Category.assoc] using (pullback.condition (f := fa) (g := fb)))

/-- The whole output retains the first original coefficient map. -/
@[reassoc] theorem atlasOriginalActionOutput_structure :
    atlasOriginalActionOutput hπ data j hj a b ≫ t = pullback.fst fa fb ≫ fa := by
  rw [atlasOriginalActionOutput, finiteGlobalSmoothPointAction_structure,
    Category.assoc, globalSmoothAtlasOriginalInput_structure]

/-- The same whole output retains the second original coefficient map. -/
@[reassoc] theorem atlasOriginalActionOutput_structure_snd :
    atlasOriginalActionOutput hπ data j hj a b ≫ t = pullback.snd fa fb ≫ fb := by
  rw [atlasOriginalActionOutput_structure, pullback.condition]

/-- The output contracts to the original action with the entire second cubic input. -/
@[reassoc] theorem atlasOriginalActionOutput_contraction :
    atlasOriginalActionOutput hπ data j hj a b ≫ (U).ι ≫ c =
      leftSmoothPointAddition W (pullback.fst fa fb ≫ original)
        (((pullback.snd fa fb ≫ smooth b) ≫ (U).ι) ≫ c) (by
          rw [Category.assoc, globalSmoothAtlasOriginalInput_structure]
          simp only [Category.assoc]
          simpa only [finiteGlobalStructure] using
            (pullback.condition (f := fa) (g := fb))) := by
  unfold atlasOriginalActionOutput
  rw [finiteGlobalSmoothPointAction_contraction]

end FLT.Mazur.WeierstrassDividedDepth
