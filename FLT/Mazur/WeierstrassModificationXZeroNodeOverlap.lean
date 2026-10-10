/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFullNodeGeometry
public import FLT.Mazur.WeierstrassModificationXFiberExteriorGeometry

/-!
# The full start-zero node intersection is the original punctured exterior

At zero divided constant the two actual tangent opens intersect exactly in
the full exterior open. Uniqueness of open subschemes identifies their scheme
pullback with the punctured slope scheme, preserving the original inclusions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (a c : R) (ha : IsUnit a) (hc : c = 0)
local notation "f" => fullFirstNodeChart a c ha
local notation "g" => fullSecondNodeChart a c ha
local notation "e" => fiberExteriorSlopeChart a c

include hc in
/-- The exterior is exactly the intersection of the two full original node images. -/
theorem fullZeroNodeOverlap_range :
    Set.range e = Set.range f ∩ Set.range g := by
  rw [fiberExteriorSlopeChart_range, range_fullFirstNodeChart, range_fullSecondNodeChart]
  simp only [fiberConicFactor, hc, map_zero, zero_mul, sub_zero,
    PrimeSpectrum.basicOpen_mul, TopologicalSpace.Opens.coe_inf]
  exact Set.inter_comm _ _

/-- The actual categorical intersection is the punctured slope scheme over the original fiber. -/
def fullZeroNodeOverlapIso : Spec (.of (SlopeOpen a)) ≅ pullback f g :=
  IsOpenImmersion.isoOfRangeEq e (pullback.fst f g ≫ f) (by
    rw [IsOpenImmersion.range_pullback_to_base_of_right]
    exact fullZeroNodeOverlap_range a c ha hc)

/-- The comparison retains the complete original inclusion, not just its underlying points. -/
@[reassoc] theorem fullZeroNodeOverlapIso_global :
    (fullZeroNodeOverlapIso a c ha hc).hom ≫ pullback.fst f g ≫ f = e := by
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The first actual overlap projection in the original node coordinates. -/
def fullZeroNodeOverlapFirst : Spec (.of (SlopeOpen a)) ⟶ Spec (.of (FullNodeOpen a c)) :=
  (fullZeroNodeOverlapIso a c ha hc).hom ≫ pullback.fst f g

/-- The second projection retains the opposite tangent node source. -/
def fullZeroNodeOverlapSecond :
    Spec (.of (SlopeOpen a)) ⟶ Spec (.of (FullNodeOpen (-a) c)) :=
  (fullZeroNodeOverlapIso a c ha hc).hom ≫ pullback.snd f g

/-- The first projection composes to the unchanged punctured exterior inclusion. -/
@[reassoc] theorem fullZeroNodeOverlapFirst_global :
    fullZeroNodeOverlapFirst a c ha hc ≫ f = e := by
  rw [fullZeroNodeOverlapFirst, Category.assoc, fullZeroNodeOverlapIso_global]

/-- The second projection has exactly the same original exterior inclusion. -/
@[reassoc] theorem fullZeroNodeOverlapSecond_global :
    fullZeroNodeOverlapSecond a c ha hc ≫ g = e := by
  rw [fullZeroNodeOverlapSecond, Category.assoc, ← pullback.condition,
    fullZeroNodeOverlapIso_global]

/-- These two actual overlap projections form a cartesian square of schemes. -/
theorem fullZeroNodeOverlap_isPullback :
    IsPullback (fullZeroNodeOverlapFirst a c ha hc) (fullZeroNodeOverlapSecond a c ha hc)
      f g := by
  apply IsPullback.of_iso_pullback
    ⟨by rw [fullZeroNodeOverlapFirst_global, fullZeroNodeOverlapSecond_global]⟩
    (fullZeroNodeOverlapIso a c ha hc)
  · rfl
  · rfl

end FLT.Mazur.WeierstrassModificationX
