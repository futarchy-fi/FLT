/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Cover.Sigma
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# The covering morphism of an fppf family

The actual disjoint union of an arbitrary small fppf covering family is a
surjective flat morphism locally of finite presentation. No finite subfamily
or quasi-compactness hypothesis is used.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SchemeFppfFamily

variable {X : Scheme.{u}} (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage X)

/-- The actual coproduct of the members of the covering family. -/
abbrev total : Scheme.{u} := ∐ 𝒰.X

/-- The jointly surjective family, regarded as a single scheme morphism. -/
def projection : total 𝒰 ⟶ X := Sigma.desc 𝒰.f

/-- Each original covering map factors through its coproduct inclusion. -/
@[reassoc (attr := simp)]
lemma inclusion_projection (i : 𝒰.I₀) :
    Sigma.ι 𝒰.X i ≫ projection 𝒰 = 𝒰.f i := Sigma.ι_comp_desc _ _

instance projection_flat : Flat (projection 𝒰) := by
  exact IsZariskiLocalAtSource.sigmaDesc (P := @Flat)
    (fun i ↦ (Scheme.Cover.map_prop (P := @Flat ⊓ @LocallyOfFinitePresentation) 𝒰 i).1)

instance projection_locallyOfFinitePresentation : LocallyOfFinitePresentation (projection 𝒰) := by
  exact IsZariskiLocalAtSource.sigmaDesc (P := @LocallyOfFinitePresentation)
    (fun i ↦ (Scheme.Cover.map_prop (P := @Flat ⊓ @LocallyOfFinitePresentation) 𝒰 i).2)

instance projection_surjective : Surjective (projection 𝒰) := by
  constructor
  intro x
  let V : X.Cover (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) := 𝒰
  obtain ⟨i, y, rfl⟩ := V.exists_eq x
  exact ⟨Sigma.ι 𝒰.X i y, by rw [← Scheme.Hom.comp_apply, inclusion_projection]⟩

/-- The coproduct morphism itself is an fppf cover. -/
lemma projection_covers :
    Presieve.singleton (projection 𝒰) ∈ Scheme.fppfPrecoverage X :=
  Scheme.Hom.singleton_mem_fppfPrecoverage _

end FLT.Mazur.SchemeFppfFamily
