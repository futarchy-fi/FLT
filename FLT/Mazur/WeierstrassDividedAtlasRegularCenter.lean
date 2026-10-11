/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedChartRegularCenter
public import FLT.Mazur.WeierstrassDividedFiniteChartStructure

/-!
# Regular deeper centers on the complete finite exterior atlas

Induction through the actual retained atlas treats the original x chart
and every successive x chart. The later scale is allowed to exceed the
atlas depth, so older members retain their exact original coordinates.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [IsDomain R] [CommRing S]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
local notation "E₀" => initialExterior (data (Fin.mk 0 (Nat.zero_lt_succ n)))

/-- Every actual exterior atlas member gives a regular principal deeper original center. -/
theorem finiteExteriorAtlas_regularCenter (j : ℕ) (hj : j ≤ n) (k : ℕ) (hk : j ≤ k)
    (i : Fin (j + 1))
    (g : Spec (.of S) ⟶ finiteExteriorAtlasObject data E₀ j hj i) [Flat g]
    (β : Coordinate W 2 →+* S)
    (he : Spec.map (CommRingCat.ofHom β) ≫ integralCurveChart W 2 =
      g ≫ finiteExteriorAtlasMap hπ data E₀ j hj i ≫
        (finiteExterior hπ data E₀ j hj).exteriorChart ≫ finiteToCurve hπ data j hj) :
    ∃ x : S, IsRegular x ∧
      (modificationChartCenter W (π ^ (start + k) * π) 2).map β = Ideal.span {x} ∧
      β (algebraMap R _ (π ^ (start + k))) ∈ Ideal.span {x} := by
  induction j with
  | zero =>
    dsimp only [finiteExteriorAtlasObject] at g he
    apply initialExterior_regularCenter hπ (data (Fin.mk 0 (Nat.zero_lt_succ n)))
      (Nat.le_add_right start k) g β
    change Spec.map (CommRingCat.ofHom β) ≫ integralCurveChart W 2 =
      g ≫ 𝟙 (E₀).carrier ≫ (E₀).exteriorChart ≫ 𝟙 (E₀).whole ≫ initialToCurve _ at he
    exact he.trans (congrArg (fun t => g ≫ t) (by
      rw [Category.id_comp (initialToCurve _), Category.id_comp]))
  | succ j ih =>
    cases i using Fin.cases with
    | zero =>
      apply stepX_regularCenter (k := start + k) hπ
        (data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj))))
        (data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj)))
        (by simpa only [Fin.val_mk, Nat.add_assoc] using
          Nat.add_le_add_left hk start) g β
      simpa only [finiteExteriorAtlas_new_toCurve] using he
    | succ i =>
      apply ih (Nat.le_of_succ_le hj) (Nat.le_trans (Nat.le_succ j) hk) i g
      simpa only [finiteExteriorAtlas_old_toCurve] using he

end FLT.Mazur.WeierstrassDividedDepth
