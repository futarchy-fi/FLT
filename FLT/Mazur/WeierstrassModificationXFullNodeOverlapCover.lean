/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFullNodeOverlapRanges
public import FLT.Mazur.BinaryOpenDescent

/-!
# The full two-piece open cover of the original tangent intersection

The punctured exterior and the conic incidence open map to the actual
categorical pullback. Both full maps detect arbitrary-target equality.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] (a c : R) (ha : IsUnit a)
local notation "f" => fullFirstNodeChart a c ha
local notation "g" => fullSecondNodeChart a c ha
local notation "b" => pullback.fst f g ≫ f
local notation "e" => fiberExteriorSlopeChart a c
local notation "t" => fiberT a c

/-- The full exterior inclusion in the categorical node overlap. -/
def fullNodeOverlapExterior : Spec (.of (SlopeOpen a)) ⟶ pullback f g :=
  IsOpenImmersion.lift b e (by
    rw [IsOpenImmersion.range_pullback_to_base_of_right]
    exact fullNodeOverlap_exterior_subset a c ha)

/-- The exterior lift preserves its original full-fiber inclusion. -/
@[reassoc] theorem fullNodeOverlapExterior_global :
    fullNodeOverlapExterior a c ha ≫ b = e := IsOpenImmersion.lift_fac _ _ _

instance fullNodeOverlapExterior_isOpenImmersion :
    IsOpenImmersion (fullNodeOverlapExterior a c ha) :=
  inferInstanceAs (IsOpenImmersion (IsOpenImmersion.lift _ _ _))

variable (hc : IsUnit c)

/-- The entire conic incidence open in the same categorical node overlap. -/
def fullNodeOverlapConic : Spec (.of (Localization.Away t)) ⟶ pullback f g :=
  IsOpenImmersion.lift b (PrincipalOpenTransport.inclusion t) (by
    rw [IsOpenImmersion.range_pullback_to_base_of_right]
    exact fullNodeOverlap_conic_subset a c ha hc)

/-- The conic lift preserves the original full-fiber incidence coordinate. -/
@[reassoc] theorem fullNodeOverlapConic_global :
    fullNodeOverlapConic a c ha hc ≫ b = PrincipalOpenTransport.inclusion t :=
  IsOpenImmersion.lift_fac _ _ _

instance fullNodeOverlapConic_isOpenImmersion :
    IsOpenImmersion (fullNodeOverlapConic a c ha hc) :=
  inferInstanceAs (IsOpenImmersion (IsOpenImmersion.lift _ _ _))

/-- The two original full pieces cover the categorical overlap. -/
theorem fullNodeOverlap_cover (x : (pullback f g : Scheme.{u})) :
    x ∈ Set.range (fullNodeOverlapExterior a c ha) ∨
      x ∈ Set.range (fullNodeOverlapConic a c ha hc) := by
  have hx : b x ∈ Set.range f ∩ Set.range g := by
    rw [← IsOpenImmersion.range_pullback_to_base_of_right g f]
    exact ⟨x, rfl⟩
  rw [fullNodeOverlap_range a c ha hc] at hx
  rcases hx with ⟨y, hy⟩ | ⟨y, hy⟩
  · left
    refine ⟨y, ?_⟩
    apply (Scheme.Hom.isOpenEmbedding b).injective
    change (fullNodeOverlapExterior a c ha ≫ b) y = b x
    rw [fullNodeOverlapExterior_global]
    exact hy
  · right
    refine ⟨y, ?_⟩
    apply (Scheme.Hom.isOpenEmbedding b).injective
    change (fullNodeOverlapConic a c ha hc ≫ b) y = b x
    rw [fullNodeOverlapConic_global]
    exact hy

/-- Equality on both complete pieces detects arbitrary-target equality on the overlap. -/
theorem fullNodeOverlap_hom_ext {Y : Scheme.{u}} (u v : pullback f g ⟶ Y)
    (he : fullNodeOverlapExterior a c ha ≫ u = fullNodeOverlapExterior a c ha ≫ v)
    (hi : fullNodeOverlapConic a c ha hc ≫ u = fullNodeOverlapConic a c ha hc ≫ v) : u = v :=
  BinaryOpenDescent.hom_ext _ _ (fullNodeOverlap_cover a c ha hc) u v he hi

end FLT.Mazur.WeierstrassModificationX
