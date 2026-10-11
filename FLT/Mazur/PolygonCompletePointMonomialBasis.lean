/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FilteredPoleBasis
public import FLT.Mazur.PolygonCompletePointExactMonomials
public import FLT.Mazur.WeightedPoleMonomials

/-!
# Monomial bases on the original marked-point complement

For each positive m the original pole space has basis 1,x,y,x²,xy,...
through order m. Both the functions and the field action are the ones
previously constructed on the specified retained field square.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve Module
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] {Y : Scheme}
  (s : Spec (.of L) ⟶ Spec (.of (PowerSeries K)))
  (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h) s)

/-- The ordered monomials of the original chosen pole-two and pole-three functions. -/
def completeCartesianPointMonomial (i : Fin n) (j : ℕ) :
    Γ((completeCartesianPointComplement K n h L s p q hs i).toScheme, ⊤) :=
  WeightedPoleMonomials.monomial
    (completeCartesianPointNewFunction K n h L s p q hs i 1 (by decide))
    (completeCartesianPointNewFunction K n h L s p q hs i 2 (by decide)) j

/-- The original ordered monomial has its specified pole bound. -/
theorem completeCartesianPointMonomial_mem (i : Fin n) (j : ℕ) :
    completeCartesianPointMonomial K n h L s p q hs i j ∈
      divisorPoleSubmodule q (completeCartesianMarking_relativeCartier K n h s p q hs i).1
        (WeightedPoleMonomials.order j) := by
  rw [mem_divisorPoleSubmodule, ← WeightedPoleMonomials.weightedOrder]
  exact completeCartesianPoint_monomial_mem K n h L s p q hs i _ _

/-- The listed monomials have nonzero values as elements of the function ring. -/
theorem completeCartesianPointMonomial_ne_zero (i : Fin n) (j : ℕ) :
    completeCartesianPointMonomial K n h L s p q hs i j ≠ 0 := by
  by_cases hj : j = 0
  · subst j
    have hx := completeCartesianPointNewFunction_ne_zero K n h L s p q hs i 1 (by decide)
    let _ := nontrivial_of_ne _ _ hx
    exact (WeightedPoleMonomials.monomial_zero _ _).trans_ne one_ne_zero
  exact completeCartesianPoint_monomial_ne_zero K n h L s p q hs i _ _
    (WeightedPoleMonomials.exponents_pos j (by omega))

/-- None of the listed monomials lies in a strictly lower original pole subspace. -/
theorem completeCartesianPointMonomial_not_mem_lt (i : Fin n) (j d : ℕ)
    (hd : d < WeightedPoleMonomials.order j) :
    completeCartesianPointMonomial K n h L s p q hs i j ∉
      divisorPoleSubmodule q (completeCartesianMarking_relativeCartier K n h s p q hs i).1 d := by
  rw [mem_divisorPoleSubmodule]
  apply completeCartesianPoint_monomial_not_mem_lt K n h L s p q hs i
  rwa [WeightedPoleMonomials.weightedOrder]

/-- The original order-m pole space has the displayed monomial basis. -/
def completeCartesianPointMonomialBasis (i : Fin n) (m : ℕ) [NeZero m] :
    Basis (Fin m) L
      (divisorPoleSubmodule q (completeCartesianMarking_relativeCartier K n h s p q hs i).1 m) :=
  FilteredPoleBasis.basisOfOrders _ (divisorPoleSubmodule_mono q _) m m
    (fun j ↦ completeCartesianPointMonomial K n h L s p q hs i j)
    (fun j ↦ WeightedPoleMonomials.order j)
    (fun _ _ hij ↦ WeightedPoleMonomials.order_strictMono hij)
    (fun j ↦ completeCartesianPointMonomial_mem K n h L s p q hs i j)
    (fun j ↦ completeCartesianPointMonomial_ne_zero K n h L s p q hs i j)
    (fun j d hd ↦ completeCartesianPointMonomial_not_mem_lt K n h L s p q hs i j d hd)
    (WeightedPoleMonomials.order_le m)
    (completeCartesianPointFunctions_finrank K n h L s p q hs i m (Nat.pos_of_neZero m))

/-- The basis contains precisely the actual monomials, with their chosen normalizations. -/
theorem completeCartesianPointMonomialBasis_apply (i : Fin n) (m : ℕ) [NeZero m]
    (j : Fin m) :
    (completeCartesianPointMonomialBasis K n h L s p q hs i m j :
      divisorComplementModule q (completeCartesianMarking K n h s p q hs i).ker) =
        completeCartesianPointMonomial K n h L s p q hs i j :=
  FilteredPoleBasis.basisOfOrders_apply ..

end FLT.Mazur.PolygonInfinitesimalStages
