/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAtlasOriginalAction
public import FLT.Mazur.WeierstrassDividedResolvedAtlasPairIso

/-!
# Whole overlap equality for the original-chart action

Two unchanged first-chart presentations of the same resolved smooth pair
have identical action outputs. Equality concerns full morphisms on any test
scheme, including nonreduced schemes, and needs no density argument.
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
  (j : ℕ) (hj : j ≤ n) (a b a' b' : Fin (j + 3))
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "c" => finiteGlobalContraction hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "smooth" => globalSmoothAtlasMap hπ data j hj
local notation "fa" => smooth a ≫ t
local notation "fb" => smooth b ≫ t
local notation "fa'" => smooth a' ≫ t
local notation "fb'" => smooth b' ≫ t
variable [IsOpenImmersion (globalIntegralAtlasMap hπ data j hj a ≫
  finiteGlobalContraction hπ data j hj)]
  [IsOpenImmersion (globalIntegralAtlasMap hπ data j hj a' ≫
    finiteGlobalContraction hπ data j hj)]

/-- The original contraction agrees on every refinement of two unchanged smooth charts. -/
theorem globalSmoothAtlasOriginalInput_common {X : Scheme}
    (f : X ⟶ (globalSmoothAtlasOpen hπ data j hj a).toScheme)
    (g : X ⟶ (globalSmoothAtlasOpen hπ data j hj a').toScheme)
    (h : f ≫ smooth a = g ≫ smooth a') :
    f ≫ globalSmoothAtlasOriginalInput hπ data j hj a =
      g ≫ globalSmoothAtlasOriginalInput hπ data j hj a' := by
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  have he := congrArg (fun z => z ≫ (U).ι ≫ c) h
  simpa only [Category.assoc, globalSmoothAtlasOriginalInput_inclusion,
    globalSmoothAtlasMap_inclusion_assoc] using he

/-- Equal full resolved pairs have equal whole action outputs in any chart presentations. -/
theorem atlasOriginalActionOutput_common {X : Scheme}
    (f : X ⟶ pullback fa fb) (g : X ⟶ pullback fa' fb')
    (h : f ≫ finiteResolvedAtlasPairInput hπ data j hj a b =
      g ≫ finiteResolvedAtlasPairInput hπ data j hj a' b') :
    f ≫ atlasOriginalActionOutput hπ data j hj a b =
      g ≫ atlasOriginalActionOutput hπ data j hj a' b' := by
  have hl := congrArg (fun z => z ≫ pullback.fst t t) h
  have hr := congrArg (fun z => z ≫ pullback.snd t t) h
  simp only [Category.assoc, finiteResolvedAtlasPairInput_fst] at hl
  simp only [Category.assoc, finiteResolvedAtlasPairInput_snd] at hr
  have ho := globalSmoothAtlasOriginalInput_common hπ data j hj a a'
    (f ≫ pullback.fst fa fb) (g ≫ pullback.fst fa' fb')
    (by simpa only [Category.assoc] using hl)
  simp only [Category.assoc] at ho
  simp only [atlasOriginalActionOutput, ← finiteGlobalSmoothPointAction_comp]
  congr 1

end FLT.Mazur.WeierstrassDividedDepth
