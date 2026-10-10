/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompatibleDegreeLifting

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

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] compatibleEval

variable (R : Type) [CommRing R] (n : ℕ) (h : 2 ≤ n) (q : ℕ)

/-- Veronese degree d is the original compatible tensor degree q*d. -/
def compatibleVeroneseDegree (d : ℕ) : Submodule (PowerSeries R) (CompatibleSections R n h) :=
  compatibleSectionDegree R n h (q * d)

/-- Reindexing by multiples retains the original unit and multiplication. -/
instance compatibleVeroneseDegree_graded :
    SetLike.GradedMonoid (compatibleVeroneseDegree R n h q) where
  one_mem := by
    change (1 : CompatibleSections R n h) ∈ compatibleSectionDegree R n h (q * 0)
    rw [Nat.mul_zero]
    exact compatibleSectionDegree_one R n h
  mul_mem := by
    intro i j s t hs ht
    change s * t ∈ compatibleSectionDegree R n h (q * (i + j))
    rw [Nat.mul_add]
    exact compatibleSectionDegree_mul R n h hs ht

/-- Finite sums of the retained compatible tensor degrees. -/
abbrev CompatibleVeroneseSections := ⨁ d : ℕ, compatibleVeroneseDegree R n h q d

/-- The positive Veronese retains a commutative ring structure. -/
instance compatibleVeroneseCommRing : CommRing (CompatibleVeroneseSections R n h q) :=
  inferInstanceAs (CommRing (⨁ d : ℕ, compatibleVeroneseDegree R n h q d))

/-- Original complete-base coefficients continue to act in degree zero. -/
instance compatibleVeroneseAlgebra :
    Algebra (PowerSeries R) (CompatibleVeroneseSections R n h q) := inferInstance

/-- Recomposition uses the original multiplication of compatible sections. -/
def compatibleVeroneseToSections :
    CompatibleVeroneseSections R n h q →+* CompatibleSections R n h :=
  DirectSum.coeRingHom (compatibleVeroneseDegree R n h q)

/-- The retained degrees evaluate through the original stage projections. -/
def compatibleVeroneseEval (m : ℕ) :
    CompatibleVeroneseSections R n h q →+* boundaryGradedSections R n h m :=
  (compatibleEval R n h m).comp (compatibleVeroneseToSections R n h q)

/-- Each retained homogeneous summand has its original actual stage section. -/
theorem compatibleVeroneseEval_of (m d : ℕ) (s : compatibleVeroneseDegree R n h q d) :
    compatibleVeroneseEval R n h q m (DirectSum.of _ d s) = compatibleEval R n h m s := by
  change compatibleEval R n h m (DirectSum.coeRingHom _ (DirectSum.of _ d s)) = _
  rw [DirectSum.coeRingHom_of]

/-- Reindexing retains every actual stage transition map. -/
theorem compatibleVeroneseEval_transition {a b : ℕ} (f : a ⟶ b) :
    (boundarySectionsMap R n h f).comp (compatibleVeroneseEval R n h q b) =
      compatibleVeroneseEval R n h q a := by
  rw [compatibleVeroneseEval, ← RingHom.comp_assoc, compatibleEval_transition]
  rfl

/-- Projection recovers each Veronese coefficient when the indexing step is positive. -/
theorem compatibleVeroneseProject_recompose (hq : 0 < q) (d : ℕ)
    (s : CompatibleVeroneseSections R n h q) :
    compatibleSectionProject R n h (q * d) (compatibleVeroneseToSections R n h q s) =
      (s d : CompatibleSections R n h) := by
  induction s using DirectSum.induction_on with
  | zero => simp only [map_zero, DFinsupp.coe_zero, Pi.zero_apply, ZeroMemClass.coe_zero]
  | of j s =>
    change compatibleSectionProject R n h (q * d)
      (DirectSum.coeRingHom (compatibleVeroneseDegree R n h q) (DirectSum.of _ j s)) = _
    rw [DirectSum.coeRingHom_of,
      compatibleSectionProject_of_mem R n h (q * d) (q * j) s s.property]
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
    Function.Injective (compatibleVeroneseToSections R n h q) := by
  intro s t he
  apply DFinsupp.ext
  intro d
  apply Subtype.ext
  have hp := congrArg (compatibleSectionProject R n h (q * d)) he
  rw [compatibleVeroneseProject_recompose R n h q hq,
    compatibleVeroneseProject_recompose R n h q hq] at hp
  exact hp

variable (K : Type) [Field K] [NeZero n]

/-- Some positive Veronese lifts all its positive degrees to every original stage. -/
theorem compatibleVeronese_positiveLifting : ∃ q : ℕ, 0 < q ∧ ∀ d : ℕ, 0 < d →
    ∀ m : ℕ, ∀ s : SectionGradedSum.grade (boundaryLine K m n h) ⊤ (q * d),
      ∃ t : compatibleVeroneseDegree K n h q d, compatibleEval K n h m t = s := by
  obtain ⟨N, hN⟩ := compatibleDegree_uniformLifting K n h
  refine ⟨N + 1, Nat.zero_lt_succ N, fun d hd m s ↦ ?_⟩
  have hb : N ≤ (N + 1) * d := le_trans (Nat.le_succ N) (Nat.le_mul_of_pos_right _ hd)
  exact hN ((N + 1) * d) hb m s

end FLT.Mazur.PolygonInfinitesimalStages
