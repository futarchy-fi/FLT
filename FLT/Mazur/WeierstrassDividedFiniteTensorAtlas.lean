/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteTensorCharts

/-!
# The complete indexed atlas after coefficient extension

Pull back every original finite atlas chart, including the retained initial
exterior and every older successive chart. Their actual coefficient
pullbacks form a finite open cover of the entire local tensor model.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (j : ℕ) (hj : j ≤ n)
local notation "E₀" => initialExterior (data (Fin.mk 0 (Nat.zero_lt_succ n)))
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "p" => pullback.snd q (finiteStructure hπ data j hj)
local notation "a" => finiteAtlasMap hπ data E₀ j hj

/-- The actual coefficient pullback of each original indexed finite atlas chart. -/
def finiteTensorAtlasObject (i : Fin (j + 2)) : Scheme := pullback (a i) p

/-- Each coefficient pullback is an actual chart of the entire finite tensor model. -/
def finiteTensorAtlasMap (i : Fin (j + 2)) :
    finiteTensorAtlasObject hπ data S j hj i ⟶ finiteTensorModel hπ data S j hj :=
  pullback.snd _ _

instance finiteTensorAtlasMap_isOpenImmersion (i : Fin (j + 2)) :
    IsOpenImmersion (finiteTensorAtlasMap hπ data S j hj i) :=
  inferInstanceAs (IsOpenImmersion (pullback.snd _ _))

/-- The indexed tensor charts retain their full original integral atlas maps. -/
theorem finiteTensorAtlasMap_isPullback (i : Fin (j + 2)) :
    IsPullback (finiteTensorAtlasMap hπ data S j hj i) (pullback.fst (a i) p) p (a i) :=
  (IsPullback.of_hasPullback _ _).flip

/-- The complete indexed tensor atlas covers every point, also at initial stage zero. -/
theorem finiteTensorAtlas_cover (z : finiteTensorModel hπ data S j hj) :
    ∃ i x, finiteTensorAtlasMap hπ data S j hj i x = z := by
  obtain ⟨i, x, hx⟩ := finiteAtlas_cover hπ data E₀ j hj (p z)
  obtain ⟨y, hy, _⟩ := Scheme.exists_preimage_of_isPullback
    (finiteTensorAtlasMap_isPullback hπ data S j hj i) z x hx.symm
  exact ⟨i, y, hy⟩

/-- The actual indexed coefficient pullbacks form a finite open cover. -/
def finiteTensorOpenCover : (finiteTensorModel hπ data S j hj).OpenCover where
  I₀ := Fin (j + 2)
  X := finiteTensorAtlasObject hπ data S j hj
  f := finiteTensorAtlasMap hπ data S j hj
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨finiteTensorAtlas_cover hπ data S j hj,
      fun i => finiteTensorAtlasMap_isOpenImmersion hπ data S j hj i⟩

/-- Every indexed tensor chart retains its whole original cubic contraction. -/
@[reassoc] theorem finiteTensorAtlasMap_toCurve (i : Fin (j + 2)) :
    finiteTensorAtlasMap hπ data S j hj i ≫ p ≫ finiteToCurve hπ data j hj =
      pullback.fst (a i) p ≫ a i ≫ finiteToCurve hπ data j hj := by
  rw [finiteTensorAtlasMap, pullback.condition_assoc]

end FLT.Mazur.WeierstrassDividedDepth
