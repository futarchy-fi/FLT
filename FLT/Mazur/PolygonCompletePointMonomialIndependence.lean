/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointAllPoleBasis

/-!
# Independence of the original complete-base monomial functions
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve FCurve.ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  divisorLineBundle ModuleSheafTensor.tensor sectionPoleMultiplicativeCoordinates
  relativePoleFunction completePointAllPoleBasis completePointHigherMonomial

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "S" => Spec (CommRingCat.of (PowerSeries K))
local notation "f" => exactVeroneseProjToBase K n h
local notation "s" => completeBaseMarking K n h i
local notation "hI" => And.left (completeBaseMarking_relativeCartier K n h i)
local notation "e" => completePointSectionFrame K n h i

/-- The ordered sequence of original constant and higher monomial functions. -/
def completePointOrderedFunction : ℕ → relativePoleComplementModule f s
  | 0 => relativePoleFunction f s hI 1 (completePointOneCanonicalBasis K n h i ())
  | m + 1 => relativePoleFunction f s hI (m + 2)
      (completePointHigherMonomial K n h i m)

/-- The original basis at each pole bound retains the same ordered function sequence. -/
theorem completePointAllPoleBasis_function (m : ℕ) (j : Fin (m + 1)) :
    relativePoleFunction f s hI (m + 1)
      (completePointAllPoleBasis K n h i m j) =
        completePointOrderedFunction K n h i j := by
  induction m with
  | zero =>
    have hj : j = 0 := Fin.ext (by omega)
    subst j
    rw [completePointAllPoleBasis_zero]
    rfl
  | succ m ih =>
    refine Fin.lastCases ?_ (fun k ↦ ?_) j
    · rw [completePointAllPoleBasis_last]
      rfl
    · rw [completePointAllPoleBasis_old, relativePoleFunction_step]
      exact ih k

/-- Every positive initial segment is independent over the actual base section ring. -/
theorem completePointOrderedFunction_initialIndependent (m : ℕ) :
    LinearIndependent Γ(S, ⊤)
      (fun j : Fin (m + 1) ↦ completePointOrderedFunction K n h i j) := by
  have hh := (completePointAllPoleBasis K n h i m).linearIndependent.map'
    (relativePoleFunctionLinear f s hI (m + 1))
    (LinearMap.ker_eq_bot.mpr (relativePoleFunction_injective f s hI (m + 1)))
  change LinearIndependent Γ(S, ⊤) (fun j ↦
    (show relativePoleComplementModule f s from
      relativePoleFunction f s hI (m + 1)
        (completePointAllPoleBasis K n h i m j))) at hh
  simpa only [completePointAllPoleBasis_function] using hh

/-- The entire original monomial sequence is independent over the base ring. -/
theorem completePointOrderedFunction_independent :
    LinearIndependent Γ(S, ⊤) (completePointOrderedFunction K n h i) := by
  classical
  apply linearIndependent_iff_finset_linearIndependent.mpr
  intro t
  let j : t → Fin (t.sup id + 1) := fun i ↦
    ⟨i, Nat.lt_succ_of_le (Finset.le_sup («f» := id) i.property)⟩
  exact (completePointOrderedFunction_initialIndependent K n h i (t.sup id)).comp j
    (fun i k hik ↦ Subtype.ext (congrArg Fin.val hik))


end FLT.Mazur.PolygonInfinitesimalStages
