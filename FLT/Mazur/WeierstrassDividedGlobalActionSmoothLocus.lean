/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalTranslationGraph
public import FLT.Mazur.WeierstrassDividedGlobalFiniteFlat
public import FLT.Mazur.SchemeSmoothLocusCartesian

/-!
# Translation preserves the full resolved smooth locus

The universal translation isomorphism preserves smoothness over its original
parameter. Cartesian smooth-locus comparison then detects the entire relative
smooth open, including exceptional components, on every scheme of points.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "fst" => pullback.fst (integralSmoothStructure W) base
local notation "snd" => pullback.snd (integralSmoothStructure W) base

/-- The smooth second-input domain is the smooth locus over the original parameter. -/
theorem finiteGlobalSecond_preimage_smooth :
    snd ⁻¹ᵁ (base).smoothLocus = (fst).smoothLocus :=
  smoothLocus_preimage_of_isPullback
    (IsPullback.of_hasPullback (integralSmoothStructure W) base).flip

/-- The entire resolved smooth open is exactly invariant under the original action. -/
theorem finiteGlobalAction_preimage_smooth :
    finiteGlobalAction hπ data j hj ⁻¹ᵁ (base).smoothLocus =
      snd ⁻¹ᵁ (base).smoothLocus := by
  let _ : IsIso (finiteGlobalTranslationGraph hπ data j hj) :=
    (finiteGlobalTranslationIso hπ data j hj).isIso_hom
  rw [← finiteGlobalTranslationGraph_snd, Scheme.Hom.comp_preimage,
    finiteGlobalSecond_preimage_smooth, Scheme.Hom.preimage_smoothLocus_eq]
  congr 1
  exact finiteGlobalTranslationGraph_fst hπ data j hj

/-- Smooth-locus invariance holds for arbitrary compatible scheme-valued inputs. -/
theorem finiteGlobalPointAction_preimage_smooth {T : Scheme.{u}}
    (a : T ⟶ (integralSmoothOpen W).toScheme)
    (b : T ⟶ finiteGlobalModel hπ data j hj)
    (h : a ≫ integralSmoothStructure W = b ≫ base) :
    finiteGlobalPointAction hπ data j hj a b h ⁻¹ᵁ (base).smoothLocus =
      b ⁻¹ᵁ (base).smoothLocus := by
  rw [finiteGlobalPointAction, Scheme.Hom.comp_preimage,
    finiteGlobalAction_preimage_smooth, ← Scheme.Hom.comp_preimage, pullback.lift_snd]

end FLT.Mazur.WeierstrassDividedDepth
