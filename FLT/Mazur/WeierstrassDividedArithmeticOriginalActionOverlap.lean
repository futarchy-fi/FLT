/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticAtlasOriginalAction
public import FLT.Mazur.WeierstrassDividedAtlasOriginalActionOverlap

/-!
# Full arithmetic overlap equality for unchanged-chart actions

Equal whole arithmetic inputs give equal quotient-valued outputs across any
two unchanged first-chart presentations. This includes all nilpotent functions
and compares the actual resolved inputs, rather than their cubic contractions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasObject globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
  globalTensorAtlasObject arithmeticTensorAtlasMap tensorIntegralAtlasProjection
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (m j : ℕ) (hj : j ≤ n) (a b a' b' : Fin (j + 3))
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
local notation "fa'" => (O a').ι ≫ chart a' ≫ s
local notation "fb'" => (O b').ι ≫ chart b' ≫ s
local notation "P" => arithmeticAtlasPairPresentation hπ data m j hj a b
local notation "P'" => arithmeticAtlasPairPresentation hπ data m j hj a' b'
local notation "I" => finiteResolvedAtlasPairInput hπ data j hj a b
local notation "I'" => finiteResolvedAtlasPairInput hπ data j hj a' b'


/-- Both integral resolved projections retain equality of the entire arithmetic inputs. -/
theorem arithmeticOriginalActionPair_common {X : Scheme}
    (f : X ⟶ pullback fa fb) (g : X ⟶ pullback fa' fb')
    (hl : f ≫ pullback.fst fa fb ≫ (O a).ι ≫ chart a =
      g ≫ pullback.fst fa' fb' ≫ (O a').ι ≫ chart a')
    (hr : f ≫ pullback.snd fa fb ≫ (O b).ι ≫ chart b =
      g ≫ pullback.snd fa' fb' ≫ (O b').ι ≫ chart b') : (f ≫ P) ≫ I = (g ≫ P') ≫ I' := by
  apply pullback.hom_ext
  · apply (cancel_mono (U).ι).mp
    simpa only [Category.assoc, arithmeticAtlasPairPresentation_first] using
      congrArg (fun morphism => morphism ≫ pullback.fst base q) hl
  · apply (cancel_mono (U).ι).mp
    simpa only [Category.assoc, arithmeticAtlasPairPresentation_second] using
      congrArg (fun morphism => morphism ≫ pullback.fst base q) hr

variable [IsOpenImmersion (globalIntegralAtlasMap hπ data j hj a ≫
  finiteGlobalContraction hπ data j hj)]
  [IsOpenImmersion (globalIntegralAtlasMap hπ data j hj a' ≫
    finiteGlobalContraction hπ data j hj)]

/-- Equal full arithmetic inputs produce the same whole quotient-valued action output. -/
theorem arithmeticAtlasOriginalActionQuotientOutput_common {X : Scheme}
    (f : X ⟶ pullback fa fb) (g : X ⟶ pullback fa' fb')
    (hl : f ≫ pullback.fst fa fb ≫ (O a).ι ≫ chart a =
      g ≫ pullback.fst fa' fb' ≫ (O a').ι ≫ chart a')
    (hr : f ≫ pullback.snd fa fb ≫ (O b).ι ≫ chart b =
      g ≫ pullback.snd fa' fb' ≫ (O b').ι ≫ chart b') :
    f ≫ arithmeticAtlasOriginalActionQuotientOutput hπ data m j hj a b =
      g ≫ arithmeticAtlasOriginalActionQuotientOutput hπ data m j hj a' b' := by
  apply pullback.hom_ext
  · simp only [Category.assoc, arithmeticAtlasOriginalActionQuotientOutput_base]
    simpa only [Category.assoc] using congrArg (fun morphism => morphism ≫ s) hl
  · simp only [Category.assoc, arithmeticAtlasOriginalActionQuotientOutput_integral,
      arithmeticAtlasOriginalActionOutput]
    simpa only [Category.assoc] using
      atlasOriginalActionOutput_common hπ data j hj a b a' b' (f ≫ P) (g ≫ P')
        (arithmeticOriginalActionPair_common hπ data m j hj a b a' b' f g hl hr)

end FLT.Mazur.WeierstrassDividedDepth
