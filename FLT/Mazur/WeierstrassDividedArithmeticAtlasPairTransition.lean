/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticAtlasPairPresentation
public import FLT.Mazur.WeierstrassDividedAtlasPairTransferLift

/-!
# Arithmetic transitions induce the exact integral atlas-pair transition

Equal arithmetic inputs in both factors give the canonical simultaneous
transition of the full integral pair. The comparison is schematic and
works over any test scheme, including nonreduced quotient schemes.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasObject globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (m j : ℕ) (hj : j ≤ n)
local notation "Q" => PolygonArithmeticStages.Quotient R π m
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "s" => finiteGlobalArithmeticStructure hπ data j hj m
local notation "projection" => pullback.fst base q
local notation "chart" => arithmeticTensorAtlasMap hπ data m j hj
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q j hj
local notation "F" a:max => (O a).ι ≫ chart a ≫ s
local notation "P" a:max b:max => arithmeticAtlasPairPresentation hπ data m j hj a b
local notation "I" a:max b:max => finiteResolvedAtlasPairInput hπ data j hj a b
variable (a b c d : Fin (j + 3))

/-- Equality of the two actual arithmetic inputs gives equality of the integral resolved pair. -/
theorem arithmeticAtlasPairPresentation_eq {T : Scheme}
    (u : T ⟶ pullback (F a) (F b)) (v : T ⟶ pullback (F c) (F d))
    (h₁ : u ≫ pullback.fst (F a) (F b) ≫ (O a).ι ≫ chart a =
      v ≫ pullback.fst (F c) (F d) ≫ (O c).ι ≫ chart c)
    (h₂ : u ≫ pullback.snd (F a) (F b) ≫ (O b).ι ≫ chart b =
      v ≫ pullback.snd (F c) (F d) ≫ (O d).ι ≫ chart d) :
    (u ≫ P a b) ≫ I a b = (v ≫ P c d) ≫ I c d := by
  apply pullback.hom_ext
  · apply (cancel_mono (base).smoothLocus.ι).mp
    simpa only [Category.assoc, arithmeticAtlasPairPresentation_first] using
      congrArg (fun f => f ≫ projection) h₁
  · apply (cancel_mono (base).smoothLocus.ι).mp
    simpa only [Category.assoc, arithmeticAtlasPairPresentation_second] using
      congrArg (fun f => f ≫ projection) h₂

/-- The actual arithmetic comparison factors through the full integral transition domain. -/
def arithmeticAtlasPairTransitionLift {T : Scheme}
    (u : T ⟶ pullback (F a) (F b)) (v : T ⟶ pullback (F c) (F d))
    (h₁ : u ≫ pullback.fst (F a) (F b) ≫ (O a).ι ≫ chart a =
      v ≫ pullback.fst (F c) (F d) ≫ (O c).ι ≫ chart c)
    (h₂ : u ≫ pullback.snd (F a) (F b) ≫ (O b).ι ≫ chart b =
      v ≫ pullback.snd (F c) (F d) ≫ (O d).ι ≫ chart d) :
    T ⟶ (atlasPairTransferOpen hπ data j hj a b c d).toScheme :=
  atlasPairTransferLift hπ data j hj a b c d (u ≫ P a b) (v ≫ P c d)
    (arithmeticAtlasPairPresentation_eq hπ data m j hj a b c d u v h₁ h₂)

/-- Transferring the first arithmetic presentation returns the second one exactly. -/
@[reassoc] theorem arithmeticAtlasPairTransitionLift_target {T : Scheme}
    (u : T ⟶ pullback (F a) (F b)) (v : T ⟶ pullback (F c) (F d))
    (h₁ : u ≫ pullback.fst (F a) (F b) ≫ (O a).ι ≫ chart a =
      v ≫ pullback.fst (F c) (F d) ≫ (O c).ι ≫ chart c)
    (h₂ : u ≫ pullback.snd (F a) (F b) ≫ (O b).ι ≫ chart b =
      v ≫ pullback.snd (F c) (F d) ≫ (O d).ι ≫ chart d) :
    arithmeticAtlasPairTransitionLift hπ data m j hj a b c d u v h₁ h₂ ≫
      atlasPairTransfer hπ data j hj a b c d = v ≫ P c d :=
  atlasPairTransferLift_target hπ data j hj a b c d (u ≫ P a b) (v ≫ P c d)
    (arithmeticAtlasPairPresentation_eq hπ data m j hj a b c d u v h₁ h₂)

/-- The lift also retains the original arithmetic presentation before changing charts. -/
@[reassoc] theorem arithmeticAtlasPairTransitionLift_source {T : Scheme}
    (u : T ⟶ pullback (F a) (F b)) (v : T ⟶ pullback (F c) (F d))
    (h₁ : u ≫ pullback.fst (F a) (F b) ≫ (O a).ι ≫ chart a =
      v ≫ pullback.fst (F c) (F d) ≫ (O c).ι ≫ chart c)
    (h₂ : u ≫ pullback.snd (F a) (F b) ≫ (O b).ι ≫ chart b =
      v ≫ pullback.snd (F c) (F d) ≫ (O d).ι ≫ chart d) :
    arithmeticAtlasPairTransitionLift hπ data m j hj a b c d u v h₁ h₂ ≫
      (atlasPairTransferOpen hπ data j hj a b c d).ι = u ≫ P a b :=
  atlasPairTransferLift_source hπ data j hj a b c d (u ≫ P a b) (v ≫ P c d)
    (arithmeticAtlasPairPresentation_eq hπ data m j hj a b c d u v h₁ h₂)

end FLT.Mazur.WeierstrassDividedDepth
