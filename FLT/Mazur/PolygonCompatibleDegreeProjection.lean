/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompatibleHomogeneousSections
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

namespace FLT.Mazur.PolygonInfinitesimalStages

open SectionGradedSum

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] compatibleEval

variable (R : Type) [CommRing R] (n : ℕ) (h : 2 ≤ n)

/-- Assemble actual stage sections with their proved transition compatibility. -/
def compatibleOfStages (s : ∀ m, boundaryGradedSections R n h m)
    (hs : ∀ {a b : ℕ} (f : a ⟶ b), boundarySectionsMap R n h f (s b) = s a) :
    CompatibleSections R n h := by
  unfold CompatibleSections
  exact ⟨s, hs⟩

/-- The assembled compatible section has precisely the specified evaluations. -/
theorem compatibleEval_ofStages (s : ∀ m, boundaryGradedSections R n h m)
    (hs : ∀ {a b : ℕ} (f : a ⟶ b), boundarySectionsMap R n h f (s b) = s a) (m : ℕ) :
    compatibleEval R n h m (compatibleOfStages R n h s hs) = s m := by
  unfold compatibleEval compatibleOfStages compatibleSectionEval CompatibleSections
  rfl

/-- Stagewise homogeneous projection preserves every transition. -/
theorem compatibleProjected_transition (k : ℕ) (s : CompatibleSections R n h)
    {a b : ℕ} (f : a ⟶ b) :
    boundarySectionsMap R n h f
      (projectDegree (boundaryLine R b n h) ⊤ k (compatibleEval R n h b s)) =
        projectDegree (boundaryLine R a n h) ⊤ k (compatibleEval R n h a s) := by
  have hp := projectDegree_pullback ((stageSystem R n h).map f)
    (boundaryLineSystemIso R n h f) k (compatibleEval R n h b s)
  change projectDegree (boundaryLine R a n h) ⊤ k
    (boundarySectionsMap R n h f (compatibleEval R n h b s)) =
      boundarySectionsMap R n h f
        (projectDegree (boundaryLine R b n h) ⊤ k (compatibleEval R n h b s)) at hp
  have hc := DFunLike.congr_fun (compatibleEval_transition R n h f) s
  change boundarySectionsMap R n h f (compatibleEval R n h b s) =
    compatibleEval R n h a s at hc
  rw [hc] at hp
  exact hp.symm

/-- Assemble the homogeneous components of an actual compatible system. -/
def compatibleProjected (k : ℕ) (s : CompatibleSections R n h) : CompatibleSections R n h :=
  compatibleOfStages R n h
    (fun m ↦ projectDegree (boundaryLine R m n h) ⊤ k (compatibleEval R n h m s))
    (compatibleProjected_transition R n h k s)

/-- The assembled projection has the actual homogeneous component at each stage. -/
theorem compatibleEval_projected (m k : ℕ) (s : CompatibleSections R n h) :
    compatibleEval R n h m (compatibleProjected R n h k s) =
      projectDegree (boundaryLine R m n h) ⊤ k (compatibleEval R n h m s) :=
  compatibleEval_ofStages R n h _ (compatibleProjected_transition R n h k s) m

/-- Project an actual compatible system onto one tensor degree at every stage. -/
def compatibleSectionProject (k : ℕ) :
    CompatibleSections R n h →+ CompatibleSections R n h where
  toFun := compatibleProjected R n h k
  map_zero' := by
    apply compatibleEval_ext R n h
    intro m
    simp only [compatibleEval_projected, map_zero]
  map_add' s t := by
    apply compatibleEval_ext R n h
    intro m
    rw [compatibleEval_projected, map_add, map_add, map_add,
      compatibleEval_projected, compatibleEval_projected]

/-- Evaluation of homogeneous projection is the original homogeneous projection at a stage. -/
theorem compatibleEval_project (m k : ℕ) (s : CompatibleSections R n h) :
    compatibleEval R n h m (compatibleSectionProject R n h k s) =
      projectDegree (boundaryLine R m n h) ⊤ k (compatibleEval R n h m s) :=
  compatibleEval_projected R n h m k s

/-- Projection lands in the indicated compatible homogeneous submodule. -/
theorem compatibleSectionProject_mem (k : ℕ) (s : CompatibleSections R n h) :
    compatibleSectionProject R n h k s ∈ compatibleSectionDegree R n h k :=
  fun m ↦ by
    rw [compatibleEval_project]
    exact projectDegree_mem _ _ _ _

/-- Projection selects the degree of any compatible homogeneous section. -/
theorem compatibleSectionProject_of_mem (k j : ℕ) (s : CompatibleSections R n h)
    (hs : s ∈ compatibleSectionDegree R n h j) :
    compatibleSectionProject R n h k s = if j = k then s else 0 := by
  apply compatibleEval_ext R n h
  intro m
  rw [compatibleEval_project]
  rw [projectDegree_of_mem _ _ k j _ (hs m)]
  split_ifs
  · rfl
  · exact (map_zero _).symm

/-- Projection of a finite sum recovers exactly its corresponding compatible coefficient. -/
theorem compatibleSectionProject_recompose (k : ℕ) (s : CompatibleGradedSections R n h) :
    compatibleSectionProject R n h k (compatibleGradedToSections R n h s) =
      (s k : CompatibleSections R n h) := by
  induction s using DirectSum.induction_on with
  | zero => simp only [map_zero, DFinsupp.coe_zero, Pi.zero_apply, ZeroMemClass.coe_zero]
  | of j s =>
    change compatibleSectionProject R n h k
      (DirectSum.coeRingHom (compatibleSectionDegree R n h) (DirectSum.of _ j s)) = _
    rw [DirectSum.coeRingHom_of, compatibleSectionProject_of_mem R n h k j s s.property]
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
    Function.Injective (compatibleGradedToSections R n h) := by
  intro s t he
  apply DFinsupp.ext
  intro k
  apply Subtype.ext
  have hp := congrArg (compatibleSectionProject R n h k) he
  rw [compatibleSectionProject_recompose, compatibleSectionProject_recompose] at hp
  exact hp

/-- Vanishing at every actual stage detects zero in the degreewise algebra. -/
theorem compatibleGradedEval_jointly_injective {s t : CompatibleGradedSections R n h}
    (he : ∀ m, compatibleGradedEval R n h m s = compatibleGradedEval R n h m t) : s = t :=
  compatibleGradedToSections_injective R n h (compatibleEval_ext R n h he)

end FLT.Mazur.PolygonInfinitesimalStages
