/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OpenImmersionIdealCorrespondence

/-!
# Full ideal extension through nested ambient opens

A closed family supported in the smaller open extends into an intermediate
open as the restriction of the original full ideal. Support is used only to
establish the factorization; the conclusion identifies the entire ideal.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.IdealSheafData

universe u

namespace FLT.Mazur.OpenIdealCover

variable {A B C : Scheme.{u}} (i : A ⟶ B) (j : B ⟶ C)
variable [IsOpenImmersion i] [IsOpenImmersion j]
variable (J : C.IdealSheafData) (hJ : Set.range J.subschemeι ⊆ Set.range (i ≫ j))

omit [IsOpenImmersion i] in
include hJ in
/-- Restricting a family supported in the smaller open remains supported in that smaller open. -/
theorem nestedOpenIdeal_support : Set.range (J.comap j).subschemeι ⊆ Set.range i := by
  rw [range_subschemeι, support_comap]
  intro y hy
  have hy' : j y ∈ Set.range J.subschemeι := by
    rw [range_subschemeι]
    exact hy
  obtain ⟨x, hx⟩ := hJ hy'
  exact ⟨x, j.isOpenEmbedding.injective hx⟩

include hJ in
/-- Extension through nested opens recovers the full restriction to the intermediate ambient. -/
theorem nestedOpenIdeal_extension : (J.comap (i ≫ j)).map i = J.comap j := by
  rw [comap_comp]
  exact open_map_comap i (J.comap j) (nestedOpenIdeal_support i j J hJ)

end FLT.Mazur.OpenIdealCover
