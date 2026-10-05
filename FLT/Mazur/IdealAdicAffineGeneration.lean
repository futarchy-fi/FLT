/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicAffineProjection
public import Mathlib.RingTheory.FiniteType

/-!
# Degree-one generation of the actual graded section algebra

Induction on ordinary ideal powers proves algebra generation before any
finiteness assertion. Finite ideal generators then give finite algebra generators.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry

universe u

namespace FLT.Mazur.IdealAdicGradedSections

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData)
variable (U : X.affineOpens)

/-- Degree-one representatives generate every homogeneous ideal-power representative. -/
lemma affineHomogeneous_mem_adjoin (n : ℕ) (r : ↥((I.ideal U) ^ n)) :
    affineHomogeneous I U n r ∈
      Algebra.adjoin Γ(X, U.1) (Set.range (affineHomogeneous I U 1)) := by
  induction n with
  | zero =>
    rw [affineHomogeneous_zero]
    exact Subalgebra.algebraMap_mem _ _
  | succ n ih =>
    obtain ⟨r, hr⟩ := r
    have hp : r ∈ (I.ideal U) ^ n * I.ideal U := by rwa [← pow_succ]
    suffices ∀ (r) (hr : r ∈ (I.ideal U) ^ n * I.ideal U),
        affineHomogeneous I U (n + 1) ⟨r, by rwa [pow_succ]⟩ ∈
          Algebra.adjoin Γ(X, U.1) (Set.range (affineHomogeneous I U 1)) from this r hp
    intro r hr
    induction hr using Submodule.smul_induction_on' with
    | smul r hr s hs =>
      have hm := (Algebra.adjoin Γ(X, U.1) (Set.range (affineHomogeneous I U 1))).mul_mem
        (ih ⟨r, hr⟩) (Algebra.subset_adjoin ⟨⟨s, by simpa using hs⟩, rfl⟩)
      rw [affineHomogeneous_mul] at hm
      exact hm
    | add r hr s hs ihr ihs =>
      exact (map_add (affineHomogeneous I U (n + 1))
        ⟨r, by rwa [pow_succ]⟩ ⟨s, by rwa [pow_succ]⟩).symm ▸
        Subalgebra.add_mem _ ihr ihs

/-- The original degree-one ideal representatives generate the full actual graded algebra. -/
lemma affine_adjoin_degree_one :
    Algebra.adjoin Γ(X, U.1) (Set.range (affineHomogeneous I U 1)) = ⊤ := by
  apply top_unique
  intro t ht
  clear ht
  induction t using DirectSum.induction_on with
  | zero => exact Subalgebra.zero_mem _
  | of n s =>
    obtain ⟨r, rfl⟩ := affineProjection_surjective I U n s
    exact affineHomogeneous_mem_adjoin I U n r
  | add s t hs ht => exact Subalgebra.add_mem _ hs ht

/-- Finite ordinary ideal generators give finite generators of the actual graded algebra. -/
theorem affineSections_finiteType_of_fg (hI : (I.ideal U).FG) :
    Algebra.FiniteType Γ(X, U.1) (Sections I U.1) := by
  have hp : ((I.ideal U) ^ 1).FG := by simpa only [pow_one] using hI
  have ht : (⊤ : Submodule Γ(X, U.1) ↥((I.ideal U) ^ 1)).FG :=
    (Submodule.fg_top _).mpr hp
  obtain ⟨s, hs⟩ := ht.map (affineHomogeneous I U 1)
  refine ⟨s, ?_⟩
  rw [← Algebra.adjoin_span, hs, Submodule.map_top]
  exact affine_adjoin_degree_one I U

/-- On a locally Noetherian scheme every actual affine graded section algebra is finite type. -/
instance affineSections_finiteType : Algebra.FiniteType Γ(X, U.1) (Sections I U.1) := by
  let _ : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  exact affineSections_finiteType_of_fg I U (IsNoetherian.noetherian _)

/-- The actual graded section algebra on an affine chart is Noetherian. -/
instance affineSections_isNoetherianRing : IsNoetherianRing (Sections I U.1) := by
  let _ : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  exact Algebra.FiniteType.isNoetherianRing Γ(X, U.1) _

end FLT.Mazur.IdealAdicGradedSections
