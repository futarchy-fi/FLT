/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticHomogeneousSections
public import FLT.Mazur.SectionGradedProjection

/-!
# Degree projections on compatible formal sections

Homogeneous projection respects every stage transition. It supplies an actual
left inverse on each degree and proves that the degreewise algebra embeds in
the ring of all compatible sections.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped DirectSum

namespace FLT.Mazur.PolygonArithmeticStages

open SectionGradedSum

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] compatibleEval

variable (A : Type) [CommRing A] (π : A) (n : ℕ) (h : 2 ≤ n)

/-- Assemble actual stage sections with their proved transition compatibility. -/
def compatibleOfStages (s : ∀ m, boundaryGradedSections A π n h m)
    (hs : ∀ {a b : ℕ} (f : a ⟶ b), boundarySectionsMap A π n h f (s b) = s a) :
    CompatibleSections A π n h := by
  unfold CompatibleSections
  exact ⟨s, hs⟩

/-- The assembled compatible section has precisely the specified evaluations. -/
theorem compatibleEval_ofStages (s : ∀ m, boundaryGradedSections A π n h m)
    (hs : ∀ {a b : ℕ} (f : a ⟶ b), boundarySectionsMap A π n h f (s b) = s a) (m : ℕ) :
    compatibleEval A π n h m (compatibleOfStages A π n h s hs) = s m := by
  unfold compatibleEval compatibleOfStages compatibleSectionEval CompatibleSections
  rfl

/-- Stagewise homogeneous projection preserves every transition. -/
theorem compatibleProjected_transition (k : ℕ) (s : CompatibleSections A π n h)
    {a b : ℕ} (f : a ⟶ b) :
    boundarySectionsMap A π n h f
      (projectDegree (boundaryLine A π b n h) ⊤ k (compatibleEval A π n h b s)) =
        projectDegree (boundaryLine A π a n h) ⊤ k (compatibleEval A π n h a s) := by
  have hp := projectDegree_pullback ((stageSystem A π n h).map f)
    (boundaryLineSystemIso A π n h f) k (compatibleEval A π n h b s)
  change projectDegree (boundaryLine A π a n h) ⊤ k
    (boundarySectionsMap A π n h f (compatibleEval A π n h b s)) =
      boundarySectionsMap A π n h f
        (projectDegree (boundaryLine A π b n h) ⊤ k (compatibleEval A π n h b s)) at hp
  have hc := DFunLike.congr_fun (compatibleEval_transition A π n h f) s
  change boundarySectionsMap A π n h f (compatibleEval A π n h b s) =
    compatibleEval A π n h a s at hc
  rw [hc] at hp
  exact hp.symm

/-- Assemble the homogeneous components of an actual compatible system. -/
def compatibleProjected (k : ℕ) (s : CompatibleSections A π n h) : CompatibleSections A π n h :=
  compatibleOfStages A π n h
    (fun m ↦ projectDegree (boundaryLine A π m n h) ⊤ k (compatibleEval A π n h m s))
    (compatibleProjected_transition A π n h k s)

/-- The assembled projection has the actual homogeneous component at each stage. -/
theorem compatibleEval_projected (m k : ℕ) (s : CompatibleSections A π n h) :
    compatibleEval A π n h m (compatibleProjected A π n h k s) =
      projectDegree (boundaryLine A π m n h) ⊤ k (compatibleEval A π n h m s) :=
  compatibleEval_ofStages A π n h _ (compatibleProjected_transition A π n h k s) m

/-- Project an actual compatible system onto one tensor degree at every stage. -/
def compatibleSectionProject (k : ℕ) :
    CompatibleSections A π n h →+ CompatibleSections A π n h where
  toFun := compatibleProjected A π n h k
  map_zero' := by
    apply compatibleEval_ext A π n h
    intro m
    simp only [compatibleEval_projected, map_zero]
  map_add' s t := by
    apply compatibleEval_ext A π n h
    intro m
    rw [compatibleEval_projected, map_add, map_add, map_add,
      compatibleEval_projected, compatibleEval_projected]

/-- Evaluation of homogeneous projection is the original homogeneous projection at a stage. -/
theorem compatibleEval_project (m k : ℕ) (s : CompatibleSections A π n h) :
    compatibleEval A π n h m (compatibleSectionProject A π n h k s) =
      projectDegree (boundaryLine A π m n h) ⊤ k (compatibleEval A π n h m s) :=
  compatibleEval_projected A π n h m k s

/-- Projection lands in the indicated compatible homogeneous submodule. -/
theorem compatibleSectionProject_mem (k : ℕ) (s : CompatibleSections A π n h) :
    compatibleSectionProject A π n h k s ∈ compatibleSectionDegree A π n h k :=
  fun m ↦ by
    rw [compatibleEval_project]
    exact projectDegree_mem _ _ _ _

/-- Projection selects the degree of any compatible homogeneous section. -/
theorem compatibleSectionProject_of_mem (k j : ℕ) (s : CompatibleSections A π n h)
    (hs : s ∈ compatibleSectionDegree A π n h j) :
    compatibleSectionProject A π n h k s = if j = k then s else 0 := by
  apply compatibleEval_ext A π n h
  intro m
  rw [compatibleEval_project]
  rw [projectDegree_of_mem _ _ k j _ (hs m)]
  split_ifs
  · rfl
  · exact (map_zero _).symm

/-- Projection of a finite sum recovers exactly its corresponding compatible coefficient. -/
theorem compatibleSectionProject_recompose (k : ℕ) (s : CompatibleGradedSections A π n h) :
    compatibleSectionProject A π n h k (compatibleGradedToSections A π n h s) =
      (s k : CompatibleSections A π n h) := by
  induction s using DirectSum.induction_on with
  | zero => simp only [map_zero, DFinsupp.coe_zero, Pi.zero_apply, ZeroMemClass.coe_zero]
  | of j s =>
    change compatibleSectionProject A π n h k
      (DirectSum.coeRingHom (compatibleSectionDegree A π n h) (DirectSum.of _ j s)) = _
    rw [DirectSum.coeRingHom_of, compatibleSectionProject_of_mem A π n h k j s s.property]
    by_cases hj : j = k
    · subst j
      rw [ite_eq_left rfl, DirectSum.of_eq_same]
    · rw [ite_eq_right hj, DirectSum.of_eq_of_ne _ _ _ (Ne.symm hj)]
      rfl
  | add s t hs ht =>
    rw [map_add, map_add, hs, ht]
    rfl

/-- The degreewise compatible algebra embeds into all compatible full sections. -/
theorem compatibleGradedToSections_injective :
    Function.Injective (compatibleGradedToSections A π n h) := by
  intro s t he
  apply DFinsupp.ext
  intro k
  apply Subtype.ext
  have hp := congrArg (compatibleSectionProject A π n h k) he
  rw [compatibleSectionProject_recompose, compatibleSectionProject_recompose] at hp
  exact hp

/-- Vanishing at every actual stage detects zero in the degreewise algebra. -/
theorem compatibleGradedEval_jointly_injective {s t : CompatibleGradedSections A π n h}
    (he : ∀ m, compatibleGradedEval A π n h m s = compatibleGradedEval A π n h m t) : s = t :=
  compatibleGradedToSections_injective A π n h (compatibleEval_ext A π n h he)

end FLT.Mazur.PolygonArithmeticStages
