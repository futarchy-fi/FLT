/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticBoundaryCharts
public import FLT.Mazur.WeierstrassDividedArithmeticTerminalIntersection

/-!
# Depth indices in the original arithmetic atlas

The retained depth a occupies index k-a+1 at stage k. All comparisons use
isomorphisms of the original tensor algebras and preserve their chart maps.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction finiteTensorAtlasObject
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (m : ℕ)
local notation "Q" => Quotient R π m
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
variable (k : ℕ) (hk : k ≤ n)

/-- The full indexed atlas, in the original arithmetic pullback orientation. -/
def arithmeticTensorAtlasMap (i : Fin (k + 3)) :
    globalTensorAtlasObject hπ data Q k hk i ⟶ finiteGlobalArithmeticStage hπ data k hk m :=
  globalTensorAtlasMap hπ data Q k hk i ≫
    (pullbackSymmetry q (finiteGlobalStructure hπ data k hk)).hom

instance arithmeticTensorAtlasMap_isOpenImmersion (i : Fin (k + 3)) :
    IsOpenImmersion (arithmeticTensorAtlasMap hπ data m k hk i) := by
  unfold arithmeticTensorAtlasMap
  infer_instance

/-- The original indexed charts cover the entire arithmetic stage. -/
theorem arithmeticTensorAtlas_cover (z : finiteGlobalArithmeticStage hπ data k hk m) :
    ∃ i x, arithmeticTensorAtlasMap hπ data m k hk i x = z := by
  let e := pullbackSymmetry q (finiteGlobalStructure hπ data k hk)
  obtain ⟨i, x, hx⟩ := globalTensorAtlas_cover hπ data Q k hk (e.inv z)
  refine ⟨i, x, ?_⟩
  change e.hom (globalTensorAtlasMap hπ data Q k hk i x) = z
  rw [hx]
  exact congrArg (fun f => f z) e.inv_hom_id

/-- The terminal tensor comparison preserves its arithmetic index one. -/
@[reassoc] theorem arithmeticTensorAtlas_terminal :
    (finiteDividedTensorAtlasIso hπ data Q k hk).hom ≫
      arithmeticTensorAtlasMap hπ data m k hk 1 =
        finiteArithmeticDividedTensorChart hπ data m k hk := by
  change _ ≫ ((finiteTensorAtlasMap hπ data Q k hk 0 ≫ _) ≫ _) = _
  rw [← Category.assoc, finiteDividedTensorAtlasIso_map_assoc]
  rfl

/-- The initial tensor comparison preserves the last arithmetic atlas index. -/
@[reassoc] theorem arithmeticTensorAtlas_initial :
    (finiteInitialTensorAtlasIso hπ data Q k hk).hom ≫
      arithmeticTensorAtlasMap hπ data m k hk (Fin.succ ⟨k + 1, by omega⟩) =
        finiteArithmeticInitialTensorChart hπ data m k hk := by
  unfold arithmeticTensorAtlasMap
  rw [← Category.assoc, globalInitialTensorChart_eq_index]
  rfl

omit [IsBezout R] in
/-- Equal stage numbers and equal finite indices give the same original tensor object. -/
theorem arithmeticTensorAtlasObject_transport (l : ℕ) (hl : l ≤ n)
    (i : Fin (k + 2)) (j : Fin (l + 2)) (h : k = l) (hij : i.val = j.val) :
    finiteTensorAtlasObject hπ data Q k hk i = finiteTensorAtlasObject hπ data Q l hl j := by
  subst l
  have he : i = j := Fin.ext hij
  subst j
  rfl

variable (a : ℕ) (ha : a < k)
local notation "d" => data (Fin.mk (a + 1) (by omega))

/-- The original retained tensor algebra at depth a, indexed at an arbitrary later stage. -/
def arithmeticRetainedTensorIso :
    Spec (.of (WeierstrassSuccessiveX.ScalarExtension W (π ^ (start + a)) π
      (Data.b3 d) (Data.b4 d) (Data.b6 d) Q)) ≅
        finiteTensorAtlasObject hπ data Q k hk ⟨k - a, by omega⟩ :=
  olderSuccessiveTensorAtlasIso hπ data Q a (by omega) (k - (a + 1)) (by omega) ≪≫
    eqToIso (by
      apply arithmeticTensorAtlasObject_transport
      · omega
      · change k - (a + 1) + 1 = k - a
        omega)

/-- Every retained depth has a map to one fixed arithmetic stage, with no implicit reindexing. -/
def arithmeticRetainedTensorChart :=
  (arithmeticRetainedTensorIso hπ data m k hk a ha).hom ≫
    arithmeticTensorAtlasMap hπ data m k hk (Fin.succ ⟨k - a, by omega⟩)

instance arithmeticRetainedTensorChart_isOpenImmersion :
    IsOpenImmersion (arithmeticRetainedTensorChart hπ data m k hk a ha) := by
  unfold arithmeticRetainedTensorChart
  infer_instance

/-- The new depth index agrees with the original retention parameter and every original map. -/
theorem arithmeticRetainedTensorChart_eq (r : ℕ) (hr : a + 1 + r ≤ n) :
    arithmeticRetainedTensorChart hπ data m (a + 1 + r) hr a (by omega) =
      finiteArithmeticOlderTensorChart hπ data m a (by omega) r hr := by
  have hi : (⟨a + 1 + r - a, by omega⟩ : Fin (a + 1 + r + 2)) =
      ⟨r + 1, by omega⟩ := by ext; dsimp; omega
  have hs : a + 1 + r - (a + 1) = r := by omega
  dsimp only [arithmeticRetainedTensorChart, arithmeticRetainedTensorIso,
    arithmeticTensorAtlasMap, globalTensorAtlasMap, globalTensorAtlasObject, Fin.cases_succ]
  simp only [Iso.trans_hom, eqToIso.hom]
  generalize_proofs at *
  generalize hs' : a + 1 + r - (a + 1) = r' at *
  clear hs'
  subst r'
  generalize hi' : a + 1 + r - a = i at *
  have he : i = r + 1 := by omega
  clear hi'
  subst i
  simp only [eqToHom_refl, Category.comp_id]
  rw [finiteArithmeticOlderTensorChart, olderGlobalTensorChart]
  simp only [← Category.assoc, olderSuccessiveTensorAtlasIso_map]

end FLT.Mazur.WeierstrassDividedDepth
