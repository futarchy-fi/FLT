/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFinalInitialComponents

/-!
# Complete initial conic parameters in the fixed final model

The affine charts of both original initial components survive index transport.
These are scheme-map equations on the entire parameters, including their origins.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth)
local notation "K" => ResidueField R

/-- Index transport retains the entire original first conic parameter. -/
@[reassoc] theorem initialGlobalConicFirstParameter_index_transport {a b : ℕ}
    (ha : a ≤ n) (hb : b ≤ n) (he : a = b)
    (hstart : 0 < start) (hk : 2 * start ≤ depth) :
    initialGlobalConicFirstParameter hπ data D a ha hstart hk ≫
        eqToHom (finiteGlobalTensorModel_index_congr hπ data K ha hb he) =
      initialGlobalConicFirstParameter hπ data D b hb hstart hk := by
  subst b
  simp only [eqToHom_refl, Category.comp_id]

/-- Index transport retains the entire original second conic parameter. -/
@[reassoc] theorem initialGlobalConicSecondParameter_index_transport {a b : ℕ}
    (ha : a ≤ n) (hb : b ≤ n) (he : a = b)
    (hstart : 0 < start) (hk : 2 * start ≤ depth) :
    initialGlobalConicSecondParameter hπ data D a ha hstart hk ≫
        eqToHom (finiteGlobalTensorModel_index_congr hπ data K ha hb he) =
      initialGlobalConicSecondParameter hπ data D b hb hstart hk := by
  subst b
  simp only [eqToHom_refl, Category.comp_id]

variable (s : ℕ) (hs : s + 1 ≤ n) (hstart : 0 < start)
  (hk : 2 * (start + s + 1) ≤ depth)
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "c" => residue R (Data.b6 d)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D start (by omega)
    (Data.b6 d) (Data.factor6 d))
local notation "transport" => eqToHom (finiteGlobalTensorModel_index_congr hπ data K
  (a := 1 + s) (b := s + 1) (by omega) hs (by omega))

/-- The full first conic parameter is the initial component's affine chart. -/
@[reassoc] theorem finalInitialComponent_first_left :
    ProjectiveLine.left K ≫ finalInitialComponent hπ data D s hs hstart hk 0 =
      (WeierstrassModificationX.conicZeroAffineIso c hc).hom ≫
        initialGlobalConicFirstParameter hπ data D (s + 1) hs hstart (by omega) := by
  change ProjectiveLine.left K ≫
    initialGlobalFirstComponent hπ data D (by omega) hstart (by omega) s (by omega) ≫
      transport = _
  rw [initialGlobalFirstComponent_left_assoc,
    initialGlobalConicFirstParameter_index_transport hπ data D _ hs (by omega)]

/-- The full second conic parameter is the initial component's affine chart. -/
@[reassoc] theorem finalInitialComponent_second_left :
    ProjectiveLine.left K ≫ finalInitialComponent hπ data D s hs hstart hk 1 =
      (WeierstrassModificationX.conicZeroAffineIso c hc).hom ≫
        initialGlobalConicSecondParameter hπ data D (s + 1) hs hstart (by omega) := by
  change ProjectiveLine.left K ≫
    initialGlobalSecondComponent hπ data D (by omega) hstart (by omega) s (by omega) ≫
      transport = _
  rw [initialGlobalSecondComponent_left_assoc,
    initialGlobalConicSecondParameter_index_transport hπ data D _ hs (by omega)]

end FLT.Mazur.WeierstrassDividedDepth
