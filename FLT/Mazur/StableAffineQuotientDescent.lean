/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.StableAffineQuotientDescentCover

/-!
# Descent through finite-group quotients to arbitrary scheme targets

The constructed local descents glue through their proved scheme-overlap
compatibility. The resulting morphism factors the original invariant map
and is unique by cancellation on the actual affine quotient charts.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.SchemeFiniteGroupQuotient

namespace FLT.Mazur.StableAffineQuotient

universe u
variable {G : Type u} [Group G] [Finite G] {X : Scheme.{u}} [X.IsSeparated]
variable (ρ : G →* Aut X) (hcover : ⨆ U : Chart ρ, U.val = ⊤)

/-- The global quotient is an epimorphism in the category of schemes. -/
instance map_epi : Epi (map ρ hcover) where
  left_cancellation a b h := by
    apply (gluedCover ρ).hom_ext
    intro U
    change chartMap ρ U ≫ a = chartMap ρ U ≫ b
    apply quotientMap_cancel (action ρ U)
    rw [← Category.assoc, ← Category.assoc]
    change localMap ρ U ≫ a = localMap ρ U ≫ b
    rw [← ι_map ρ hcover U, Category.assoc, Category.assoc, h]

variable {Y : Scheme.{u}} (f : X ⟶ Y) (hf : ∀ g : G, (ρ g).hom ≫ f = f)

/-- The actual descended morphism to an arbitrary scheme target. -/
def desc : glued ρ ⟶ Y :=
  (descentQuotientCover ρ f hf hcover).glueMorphisms
    (targetLocalDesc ρ f hf) (targetLocalDesc_compatible ρ f hf)

/-- The global descent restricts to each of the constructed local affine-target descents. -/
@[reassoc]
lemma chartMap_desc (c : DescentChart ρ f) :
    chartMap ρ c.val.1 ≫ desc ρ hcover f hf = targetLocalDesc ρ f hf c :=
  (descentQuotientCover ρ f hf hcover).ι_glueMorphisms _ _ c

/-- The descended morphism factors the original invariant map as a scheme morphism. -/
@[reassoc]
lemma desc_fac : map ρ hcover ≫ desc ρ hcover f hf = f := by
  apply (descentSourceCover ρ f hf hcover).hom_ext
  intro c
  change c.val.1.val.ι ≫ map ρ hcover ≫ desc ρ hcover f hf = c.val.1.val.ι ≫ f
  rw [ι_map_assoc]
  change (quotientMap (action ρ c.val.1) ≫ chartMap ρ c.val.1) ≫ _ = _
  rw [Category.assoc, chartMap_desc, targetLocalDesc_fac]

include hf in
/-- Every invariant morphism to any scheme factors uniquely through the global quotient. -/
theorem existsUnique_desc : ∃! k : glued ρ ⟶ Y, map ρ hcover ≫ k = f := by
  refine ⟨desc ρ hcover f hf, desc_fac ρ hcover f hf, ?_⟩
  intro k hk
  rw [← cancel_epi (map ρ hcover), hk, desc_fac]

/-- Invariance is exactly the condition for unique scheme-level factorization. -/
theorem invariant_iff_existsUnique_desc :
    (∀ g : G, (ρ g).hom ≫ f = f) ↔ ∃! k : glued ρ ⟶ Y, map ρ hcover ≫ k = f := by
  constructor
  · exact existsUnique_desc ρ hcover f
  · rintro ⟨k, hk, _⟩ g
    rw [← hk, map_invariant_assoc]

end FLT.Mazur.StableAffineQuotient
