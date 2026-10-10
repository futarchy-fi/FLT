/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderIndexedNodeCover
public import FLT.Mazur.WeierstrassSuccessiveXResidueZeroNodeDisjoint

/-!
# Descent on the original retained indexed chart at zero divided constant

The two ordered positive-depth node opens are disjoint when the divided
constant vanishes. Arbitrary maps on them glue on the actual finite cover.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "c" => residue R (Data.b6 e)
local notation "N" => Spec (CommRingCat.of (MiddleNodeOpen c))
local notation "U" => olderIndexedNodeOpenCover hπ data D j hj r hr hk0 hk
local notation "f" => olderIndexedNodeMap hπ data D j hj r hr hk0 hk
local notation "Obj" => globalTensorAtlasObject hπ data K (j + 1 + r) hr
  (Fin.succ (Fin.mk (r + 1) (by omega)))

/-- Disjointness holds in the exact original indexed atlas object. -/
theorem olderZeroConstantIndexedNodes_disjoint (hc : c = 0) :
    Disjoint (Set.range (f 0)) (Set.range (f 1)) := by
  let v := olderSuccessiveTensorAtlasIso hπ data K j hj r hr
  change Disjoint (Set.range (v.hom ∘ _)) (Set.range (v.hom ∘ _))
  rw [Set.range_comp, Set.range_comp]
  apply Set.disjoint_image_of_injective v.hom.homeomorph.injective
  exact residueMiddleZeroNodeCharts_disjoint D (start + j) hk0 hk
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) hc

variable {Y : Scheme.{u}}
  (a b : Spec (.of (MiddleNodeOpen
    (residue R (Data.b6 (data ⟨j + 1, Nat.lt_succ_of_le hj⟩))))) ⟶ Y)

/-- A pair of node maps is indexed by the original two-member cover. -/
def olderZeroConstantNodeFamily (i : Fin 2) : N ⟶ Y :=
  if i = 0 then a else b

/-- The arbitrary pair agrees on all four actual scheme intersections. -/
theorem olderZeroConstantNodeFamily_compatible (hc : c = 0) (i l : Fin 2) :
    pullback.fst (f i) (f l) ≫
        olderZeroConstantNodeFamily data j hj a b i =
      pullback.snd (f i) (f l) ≫
        olderZeroConstantNodeFamily data j hj a b l := by
  fin_cases i <;> fin_cases l
  · congr 1
    exact (cancel_mono (f 0)).mp pullback.condition
  · change pullback.fst (f 0) (f 1) ≫ a = pullback.snd (f 0) (f 1) ≫ b
    let _ : IsEmpty (pullback (f 0) (f 1) : Scheme.{u}) := Scheme.isEmpty_pullback _ _
      (olderZeroConstantIndexedNodes_disjoint hπ data D j hj r hr hk0 hk hc)
    exact isInitialOfIsEmpty.hom_ext _ _
  · change pullback.fst (f 1) (f 0) ≫ b = pullback.snd (f 1) (f 0) ≫ a
    let _ : IsEmpty (pullback (f 1) (f 0) : Scheme.{u}) := Scheme.isEmpty_pullback _ _
      (olderZeroConstantIndexedNodes_disjoint hπ data D j hj r hr hk0 hk hc).symm
    exact isInitialOfIsEmpty.hom_ext _ _
  · congr 1
    exact (cancel_mono (f 1)).mp pullback.condition

/-- The arbitrary node maps descend on the complete original retained indexed chart. -/
def olderZeroConstantIndexedDesc (hc : c = 0) : Obj ⟶ Y :=
  (U).glueMorphisms (olderZeroConstantNodeFamily data j hj a b)
    (olderZeroConstantNodeFamily_compatible hπ data D j hj r hr hk0 hk a b hc)

/-- The descended morphism has the specified first original node restriction. -/
@[reassoc] theorem olderZeroConstantIndexedDesc_first (hc : c = 0) :
    f 0 ≫ olderZeroConstantIndexedDesc hπ data D j hj r hr hk0 hk a b hc = a := by
  change (U).f (0 : Fin 2) ≫ (U).glueMorphisms _ _ =
    olderZeroConstantNodeFamily data j hj a b 0
  exact (U).ι_glueMorphisms _ _ (0 : Fin 2)

/-- The second ordered node restriction is also unchanged by descent. -/
@[reassoc] theorem olderZeroConstantIndexedDesc_second (hc : c = 0) :
    f 1 ≫ olderZeroConstantIndexedDesc hπ data D j hj r hr hk0 hk a b hc = b := by
  change (U).f (1 : Fin 2) ≫ (U).glueMorphisms _ _ =
    olderZeroConstantNodeFamily data j hj a b 1
  exact (U).ι_glueMorphisms _ _ (1 : Fin 2)

/-- The two full original node restrictions determine the descended map uniquely. -/
theorem olderZeroConstantIndexedDesc_unique (hc : c = 0) (d : Obj ⟶ Y)
    (h₁ : f 0 ≫ d = a) (h₂ : f 1 ≫ d = b) :
    d = olderZeroConstantIndexedDesc hπ data D j hj r hr hk0 hk a b hc := by
  apply (U).hom_ext
  intro i
  change Fin 2 at i
  fin_cases i
  · exact h₁.trans (olderZeroConstantIndexedDesc_first hπ data D j hj r hr hk0 hk a b hc).symm
  · exact h₂.trans (olderZeroConstantIndexedDesc_second hπ data D j hj r hr hk0 hk a b hc).symm

end FLT.Mazur.WeierstrassDividedDepth
