/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedCoefficientActionSmoothLocus
public import FLT.Mazur.WeierstrassDividedGlobalCoefficientSmoothOrbit
public import FLT.Mazur.WeierstrassDividedCoefficientSmoothLocus

/-!
# Intrinsic laws and the original orbit on the extended resolved smooth open

The restricted coefficient action has the original zero, inverse and addition.
Its orbit comparison uses the already constructed original coefficient embedding.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
  (S : Type u) [CommRing S] [Algebra R S]
local notation "V" => W.map (algebraMap R S)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "g" => pullback.fst q base
local notation "U" => (g).smoothLocus
local notation "emb" => finiteGlobalCoefficientSmoothOrbitToSmooth hπ data S j hj

/-- The actual extended zero fixes every point of the full extended smooth open. -/
theorem finiteGlobalCoefficientSmoothPointAction_zero {T : Scheme.{u}}
    (b : T ⟶ (U).toScheme) :
    finiteGlobalCoefficientSmoothPointAction hπ data j hj S
      (b ≫ (U).ι ≫ g ≫ integralSmoothZero V) b
      (by rw [Category.assoc, Category.assoc, Category.assoc,
        integralSmoothZero_structure, Category.comp_id]) = b := by
  apply (cancel_mono (U).ι).mp
  rw [finiteGlobalCoefficientSmoothPointAction_inclusion]
  simpa only [Category.assoc] using
    finiteGlobalCoefficientPointAction_zero hπ data j hj S (b ≫ (U).ι)

/-- Intrinsic negative translation cancels on all extended resolved components. -/
theorem finiteGlobalCoefficientSmoothPointAction_neg_cancel {T : Scheme.{u}}
    (a : T ⟶ (integralSmoothOpen V).toScheme) (b : T ⟶ (U).toScheme)
    (h : a ≫ integralSmoothStructure V = b ≫ (U).ι ≫ g) :
    finiteGlobalCoefficientSmoothPointAction hπ data j hj S (a ≫ integralSmoothNegation V)
      (finiteGlobalCoefficientSmoothPointAction hπ data j hj S a b h)
      (by rw [Category.assoc, integralSmoothNegation_structure,
        finiteGlobalCoefficientSmoothPointAction_structure]) = b := by
  apply (cancel_mono (U).ι).mp
  simp only [finiteGlobalCoefficientSmoothPointAction_inclusion]
  exact finiteGlobalCoefficientPointAction_neg_cancel hπ data j hj S a (b ≫ (U).ι)
    (by simpa only [Category.assoc] using h)

/-- Extended original addition acts associatively on the full extended smooth model. -/
theorem finiteGlobalCoefficientSmoothPointAction_assoc {T : Scheme.{u}}
    (a b : T ⟶ (integralSmoothOpen V).toScheme) (c : T ⟶ (U).toScheme)
    (hab : a ≫ integralSmoothStructure V = b ≫ integralSmoothStructure V)
    (hbc : b ≫ integralSmoothStructure V = c ≫ (U).ι ≫ g) :
    finiteGlobalCoefficientSmoothPointAction hπ data j hj S (smoothPairPointAddition V a b hab) c
        (by rw [smoothPairPointAddition_structure]; exact hab.trans hbc) =
      finiteGlobalCoefficientSmoothPointAction hπ data j hj S a
        (finiteGlobalCoefficientSmoothPointAction hπ data j hj S b c hbc)
        (by rw [finiteGlobalCoefficientSmoothPointAction_structure]; exact hab) := by
  apply (cancel_mono (U).ι).mp
  simp only [finiteGlobalCoefficientSmoothPointAction_inclusion]
  exact finiteGlobalCoefficientPointAction_assoc hπ data j hj S a b (c ≫ (U).ι) hab
    (by simpa only [Category.assoc] using hbc)

/-- The existing original orbit is equivariant for its intrinsic group law. -/
theorem finiteGlobalCoefficientSmoothPointAction_originalOrbit {T : Scheme.{u}}
    (a b : T ⟶ (integralSmoothOpen V).toScheme)
    (h : a ≫ integralSmoothStructure V = b ≫ integralSmoothStructure V) :
    finiteGlobalCoefficientSmoothPointAction hπ data j hj S a (b ≫ emb)
        (by rw [Category.assoc, finiteGlobalCoefficientSmoothOrbitToSmooth_inclusion_assoc,
          finiteGlobalSmoothCoefficientEmbedding_structure]; exact h) =
      smoothPairPointAddition V a b h ≫ emb := by
  apply (cancel_mono (U).ι).mp
  simp only [finiteGlobalCoefficientSmoothPointAction_inclusion, Category.assoc,
    finiteGlobalCoefficientSmoothOrbitToSmooth_inclusion]
  exact finiteGlobalCoefficientPointAction_smoothEmbedding hπ data j hj S a b h

end FLT.Mazur.WeierstrassDividedDepth
