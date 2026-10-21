/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderGlobalTensorCharts

/-!
# Retained depth indices after arbitrary scalar extension

The original successive tensor chart at depth a is identified with its full
indexed chart at any later stage, without changing its map to the model.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure finiteTensorAtlasObject
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (k : ℕ) (hk : k ≤ n)

omit [IsBezout R] in
/-- Equal stage numbers and equal finite indices give the same original tensor object. -/
theorem retainedTensorAtlasObject_transport (l : ℕ) (hl : l ≤ n)
    (i : Fin (k + 2)) (j : Fin (l + 2)) (h : k = l) (hij : i.val = j.val) :
    finiteTensorAtlasObject hπ data S k hk i = finiteTensorAtlasObject hπ data S l hl j := by
  subst l
  have he : i = j := Fin.ext hij
  subst j
  rfl

variable (a : ℕ) (ha : a < k)
local notation "d" => data (Fin.mk (a + 1) (by omega))

/-- The original retained tensor algebra at depth a, indexed at an arbitrary later stage. -/
def retainedTensorAtlasIso :
    Spec (.of (WeierstrassSuccessiveX.ScalarExtension W (π ^ (start + a)) π
      (Data.b3 d) (Data.b4 d) (Data.b6 d) S)) ≅
        finiteTensorAtlasObject hπ data S k hk ⟨k - a, by omega⟩ :=
  olderSuccessiveTensorAtlasIso hπ data S a (by omega) (k - (a + 1)) (by omega) ≪≫
    eqToIso (by
      apply retainedTensorAtlasObject_transport
      · omega
      · change k - (a + 1) + 1 = k - a
        omega)

/-- Every retained depth maps to one fixed scalar-extended stage at its exact index. -/
def retainedGlobalTensorChart :=
  (retainedTensorAtlasIso hπ data S k hk a ha).hom ≫
    globalTensorAtlasMap hπ data S k hk (Fin.succ ⟨k - a, by omega⟩)

instance retainedGlobalTensorChart_isOpenImmersion :
    IsOpenImmersion (retainedGlobalTensorChart hπ data S k hk a ha) := by
  unfold retainedGlobalTensorChart
  infer_instance

/-- The new depth index agrees with the original retention parameter and every original map. -/
theorem retainedGlobalTensorChart_eq (r : ℕ) (hr : a + 1 + r ≤ n) :
    retainedGlobalTensorChart hπ data S (a + 1 + r) hr a (by omega) =
      olderGlobalTensorChart hπ data S a (by omega) r hr := by
  have hi : (⟨a + 1 + r - a, by omega⟩ : Fin (a + 1 + r + 2)) =
      ⟨r + 1, by omega⟩ := by ext; dsimp; omega
  have hs : a + 1 + r - (a + 1) = r := by omega
  dsimp only [retainedGlobalTensorChart, retainedTensorAtlasIso,
    globalTensorAtlasMap, globalTensorAtlasObject, Fin.cases_succ]
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
  rw [olderGlobalTensorChart]
  simp only [← Category.assoc, olderSuccessiveTensorAtlasIso_map]

end FLT.Mazur.WeierstrassDividedDepth
