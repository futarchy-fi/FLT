/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointHigherMonomials
public import FLT.Mazur.PolygonCompletePointSpecifiedBasis
public import FLT.Mazur.RelativePoleComplementLinear

/-!
# Actual monomial bases in every positive complete-base degree
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve FCurve.ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  divisorLineBundle ModuleSheafTensor.tensor sectionPoleMultiplicativeCoordinates
  relativePoleFunction completePointSpecifiedBasis completePointHigherMonomial

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "S" => Spec (CommRingCat.of (PowerSeries K))
local notation "f" => exactVeroneseProjToBase K n h
local notation "s" => completeBaseMarking K n h i
local notation "hI" => And.left (completeBaseMarking_relativeCartier K n h i)
local notation "e" => completePointSectionFrame K n h i

/-- Append one last index without changing any preceding finite index. -/
def completePointPoleIndexSucc (n : ℕ) : Fin n ⊕ Unit ≃ Fin (n + 1) :=
  (Equiv.sumCongr (Equiv.refl _) (Equiv.ofUnique Unit (Fin 1))).trans finSumFinEquiv

/-- Old indices retain their position in the extended basis. -/
theorem completePointPoleIndexSucc_old (n : ℕ) (j : Fin n) :
    (completePointPoleIndexSucc n).symm j.castSucc = Sum.inl j := by
  simp only [completePointPoleIndexSucc, Equiv.symm_trans_apply,
    finSumFinEquiv_symm_apply_castSucc, Equiv.sumCongr_symm, Equiv.sumCongr_apply,
    Sum.map_inl, Equiv.refl_symm, Equiv.refl_apply]

/-- The new vector occupies the last position. -/
theorem completePointPoleIndexSucc_last (n : ℕ) :
    (completePointPoleIndexSucc n).symm (Fin.last n) = Sum.inr () := by
  simp only [completePointPoleIndexSucc, Equiv.symm_trans_apply, finSumFinEquiv_symm_last,
    Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inr]

/-- A basis in every original positive pole degree, built from actual monomial sections. -/
def completePointAllPoleBasis : (m : ℕ) → Module.Basis (Fin (m + 1)) Γ(S, ⊤)
    (ModuleRingH (f).appTop.hom
      (tensorPower (completePointLine K n h i) (m + 1)) 0)
  | 0 => (completePointOneCanonicalBasis K n h i).reindex (Equiv.ofUnique Unit (Fin 1))
  | m + 1 => (completePointSpecifiedBasis K n h i (m + 1)
      (completePointAllPoleBasis m) (completePointHigherMonomial K n h i m)
      (completePointHigherMonomial_coefficient K n h i m)).reindex
        (completePointPoleIndexSucc (m + 1))

/-- The first basis retains the original canonical degree-one vector. -/
theorem completePointAllPoleBasis_zero (j : Fin 1) :
    completePointAllPoleBasis K n h i 0 j = completePointOneCanonicalBasis K n h i () := by
  rw [completePointAllPoleBasis, Module.Basis.reindex_apply]

/-- Each old vector enters the next degree by the original divisor step. -/
theorem completePointAllPoleBasis_old (m : ℕ) (j : Fin (m + 1)) :
    completePointAllPoleBasis K n h i (m + 1) j.castSucc =
      divisorPowerRingStep (f).appTop.hom hI (m + 1)
        (completePointAllPoleBasis K n h i m j) := by
  rw [completePointAllPoleBasis, Module.Basis.reindex_apply, completePointPoleIndexSucc_old]
  exact completePointSpecifiedBasis_old _ _ _ _ _ _ _ _ j

/-- The last vector is the constructed actual monomial of that degree. -/
theorem completePointAllPoleBasis_last (m : ℕ) :
    completePointAllPoleBasis K n h i (m + 1) (Fin.last (m + 1)) =
      completePointHigherMonomial K n h i m := by
  rw [completePointAllPoleBasis, Module.Basis.reindex_apply, completePointPoleIndexSucc_last]
  exact completePointSpecifiedBasis_new _ _ _ _ _ _ _ _


end FLT.Mazur.PolygonInfinitesimalStages
