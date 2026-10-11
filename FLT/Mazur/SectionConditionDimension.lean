/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionConditionAcyclic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Dimension loss under a nonzero one-dimensional condition

A nonzero evaluation in a one-dimensional quotient is surjective. Its actual
kernel loses exactly one global section and retains H¹ vanishing. These are
the cohomological steps used when subtracting a point from an acyclic line.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

variable {k : Type} [Field k] {X : Scheme} (f : X ⟶ Spec (.of k))
  (S : ShortComplex X.Modules) (hS : S.ShortExact)

/-- A nonzero section value spans any quotient with one-dimensional H⁰. -/
theorem sections_surjective_of_quotient_rank_one
    (hr : Module.finrank k (ModuleScalarH f S.X₃ 0) = 1)
    (s : Γ(S.X₂, ⊤)) (hs : S.g.app ⊤ s ≠ 0) :
    Function.Surjective (S.g.app ⊤) := by
  have hn : moduleScalarHMap f S.g 0 ≠ 0 := by
    intro hz
    have he := moduleScalarH0Equiv_naturality f S.g
      ((moduleScalarH0Equiv f S.X₂).symm s)
    rw [hz, LinearMap.zero_apply, map_zero, LinearEquiv.apply_symm_apply] at he
    exact hs he.symm
  have hsur := surjective_of_nonzero_of_finrank_eq_one hr hn
  intro t
  obtain ⟨x, hx⟩ := hsur ((moduleScalarH0Equiv f S.X₃).symm t)
  refine ⟨moduleScalarH0Equiv f S.X₂ x, ?_⟩
  rw [← moduleScalarH0Equiv_naturality, hx, LinearEquiv.apply_symm_apply]

include hS in
/-- Exact dimension loss for an arbitrary surjective section condition. -/
theorem kernel_h0_finrank_add_of_sections_surjective
    [Module.Finite k (ModuleScalarH f S.X₂ 0)]
    (hg : Function.Surjective (S.g.app ⊤)) :
    Module.finrank k (ModuleScalarH f S.X₁ 0) +
      Module.finrank k (ModuleScalarH f S.X₃ 0) =
        Module.finrank k (ModuleScalarH f S.X₂ 0) := by
  let hAb := CoherentDevissage.moduleToSheaf_shortExact hS
  have h := (moduleScalarHMap f S.g 0).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr
    (moduleScalarHMap_zero_surjective_of_sections f S hg), finrank_top,
    (moduleScalarH_exact₂ S hAb f 0).linearMap_ker_eq,
    LinearMap.finrank_range_of_inj (moduleScalarHMap_zero_injective S hAb f)] at h
  omega

include hS in
/-- A nonzero rank-one condition cuts H⁰ by one and preserves acyclicity. -/
theorem kernel_acyclic_rank_drop_one
    [Subsingleton (ModuleScalarH f S.X₂ 1)]
    [Module.Finite k (ModuleScalarH f S.X₂ 0)]
    (hr : Module.finrank k (ModuleScalarH f S.X₃ 0) = 1)
    (s : Γ(S.X₂, ⊤)) (hs : S.g.app ⊤ s ≠ 0) :
    Subsingleton (ModuleScalarH f S.X₁ 1) ∧
      Module.finrank k (ModuleScalarH f S.X₁ 0) + 1 =
        Module.finrank k (ModuleScalarH f S.X₂ 0) := by
  have hg := sections_surjective_of_quotient_rank_one f S hr s hs
  refine ⟨kernel_h1_vanishing_of_sections_surjective f S hS hg, ?_⟩
  simpa only [hr] using kernel_h0_finrank_add_of_sections_surjective f S hS hg

end FLT.Mazur.FCurve
