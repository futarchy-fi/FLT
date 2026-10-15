/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticDegreeLifting

/-!
# A positive Veronese of the constructed compatible algebra

Keep precisely the original tensor degrees divisible by a chosen positive
integer, retaining their multiplication and all original stage evaluations.
A sufficiently positive choice lifts every positive Veronese degree. The
unchanged degree-zero part still requires a separate coefficient comparison.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped DirectSum

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] compatibleEval

variable (A : Type) [CommRing A] (π : A) (n : ℕ) (h : 2 ≤ n) (q : ℕ)

/-- Veronese degree d is the original compatible tensor degree q*d. -/
def compatibleVeroneseDegree (d : ℕ) : Submodule (A) (CompatibleSections A π n h) :=
  compatibleSectionDegree A π n h (q * d)

/-- Reindexing by multiples retains the original unit and multiplication. -/
instance compatibleVeroneseDegree_graded :
    SetLike.GradedMonoid (compatibleVeroneseDegree A π n h q) where
  one_mem := by
    change (1 : CompatibleSections A π n h) ∈ compatibleSectionDegree A π n h (q * 0)
    rw [Nat.mul_zero]
    exact compatibleSectionDegree_one A π n h
  mul_mem := by
    intro i j s t hs ht
    change s * t ∈ compatibleSectionDegree A π n h (q * (i + j))
    rw [Nat.mul_add]
    exact compatibleSectionDegree_mul A π n h hs ht

/-- Finite sums of the retained compatible tensor degrees. -/
abbrev CompatibleVeroneseSections := ⨁ d : ℕ, compatibleVeroneseDegree A π n h q d

/-- The positive Veronese retains a commutative ring structure. -/
instance compatibleVeroneseCommRing : CommRing (CompatibleVeroneseSections A π n h q) :=
  inferInstanceAs (CommRing (⨁ d : ℕ, compatibleVeroneseDegree A π n h q d))

/-- Original integral-base coefficients continue to act in degree zero. -/
instance compatibleVeroneseAlgebra :
    Algebra (A) (CompatibleVeroneseSections A π n h q) := inferInstance

/-- Recomposition uses the original multiplication of compatible sections. -/
def compatibleVeroneseToSections :
    CompatibleVeroneseSections A π n h q →+* CompatibleSections A π n h :=
  DirectSum.coeRingHom (compatibleVeroneseDegree A π n h q)

/-- The retained degrees evaluate through the original stage projections. -/
def compatibleVeroneseEval (m : ℕ) :
    CompatibleVeroneseSections A π n h q →+* boundaryGradedSections A π n h m :=
  (compatibleEval A π n h m).comp (compatibleVeroneseToSections A π n h q)

/-- Each retained homogeneous summand has its original actual stage section. -/
theorem compatibleVeroneseEval_of (m d : ℕ) (s : compatibleVeroneseDegree A π n h q d) :
    compatibleVeroneseEval A π n h q m (DirectSum.of _ d s) = compatibleEval A π n h m s := by
  change compatibleEval A π n h m (DirectSum.coeRingHom _ (DirectSum.of _ d s)) = _
  rw [DirectSum.coeRingHom_of]

/-- Reindexing retains every actual stage transition map. -/
theorem compatibleVeroneseEval_transition {a b : ℕ} (f : a ⟶ b) :
    (boundarySectionsMap A π n h f).comp (compatibleVeroneseEval A π n h q b) =
      compatibleVeroneseEval A π n h q a := by
  rw [compatibleVeroneseEval, ← RingHom.comp_assoc, compatibleEval_transition]
  rfl

/-- Projection recovers each Veronese coefficient when the indexing step is positive. -/
theorem compatibleVeroneseProject_recompose (hq : 0 < q) (d : ℕ)
    (s : CompatibleVeroneseSections A π n h q) :
    compatibleSectionProject A π n h (q * d) (compatibleVeroneseToSections A π n h q s) =
      (s d : CompatibleSections A π n h) := by
  induction s using DirectSum.induction_on with
  | zero => simp only [map_zero, DFinsupp.coe_zero, Pi.zero_apply, ZeroMemClass.coe_zero]
  | of j s =>
    change compatibleSectionProject A π n h (q * d)
      (DirectSum.coeRingHom (compatibleVeroneseDegree A π n h q) (DirectSum.of _ j s)) = _
    rw [DirectSum.coeRingHom_of,
      compatibleSectionProject_of_mem A π n h (q * d) (q * j) s s.property]
    by_cases hj : j = d
    · subst j
      rw [ite_eq_left rfl, DirectSum.of_eq_same]
    · have hqj : q * j ≠ q * d := fun he ↦ hj (Nat.eq_of_mul_eq_mul_left hq he)
      rw [ite_eq_right hqj, DirectSum.of_eq_of_ne _ _ _ (Ne.symm hj)]
      rfl
  | add s t hs ht =>
    rw [map_add, map_add, hs, ht]
    rfl

/-- The positive Veronese embeds in the original compatible section ring. -/
theorem compatibleVeroneseToSections_injective (hq : 0 < q) :
    Function.Injective (compatibleVeroneseToSections A π n h q) := by
  intro s t he
  apply DFinsupp.ext
  intro d
  apply Subtype.ext
  have hp := congrArg (compatibleSectionProject A π n h (q * d)) he
  rw [compatibleVeroneseProject_recompose A π n h q hq,
    compatibleVeroneseProject_recompose A π n h q hq] at hp
  exact hp

variable [IsNoetherianRing A] [IsLocalRing A] [IsDomain A] [NeZero n]
  (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)

include hne hgen in
/-- Some positive Veronese lifts all its positive degrees to every original stage. -/
theorem compatibleVeronese_positiveLifting : ∃ q : ℕ, 0 < q ∧ ∀ d : ℕ, 0 < d →
    ∀ m : ℕ, ∀ s : SectionGradedSum.grade (boundaryLine A π m n h) ⊤ (q * d),
      ∃ t : compatibleVeroneseDegree A π n h q d, compatibleEval A π n h m t = s := by
  obtain ⟨N, hN⟩ := compatibleDegree_uniformLifting A π n h hne hgen
  refine ⟨N + 1, Nat.zero_lt_succ N, fun d hd m s ↦ ?_⟩
  have hb : N ≤ (N + 1) * d := le_trans (Nat.le_succ N) (Nat.le_mul_of_pos_right _ hd)
  exact hN ((N + 1) * d) hb m s

end FLT.Mazur.PolygonArithmeticStages
