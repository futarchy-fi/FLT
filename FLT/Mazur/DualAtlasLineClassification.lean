/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DualAtlasSectionForwardReverse
public import FLT.Mazur.DualAtlasSectionReverseForward
public import FLT.Mazur.LocallySplitLineAtlasIndependence
public import FLT.Mazur.LocallySplitSheafMonomorphism

/-!
# Classification of retained line inclusions by the dual projective atlas

Equality of actual atlas sections is equivalent to an isomorphism of the
original source lines commuting with their inclusions. Both directions use
the constructed forward line and its proved recovery isomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] FLT.Mazur.CoherentSubmoduleGluing.data
  FLT.Mazur.LocallySplitLineAtlasSection.morphism
namespace FLT.Mazur.LocallySplitLineAtlasSection
open FCurve SplitLineAffineNeighborhood
variable {X : Scheme.{u}} {L N M : X.Modules} (s : L ⟶ M) (t : N ⟶ M)
  (hL : LocallyFreeRankOne L) (hN : LocallyFreeRankOne N)
  (hs : LocallySplit s) (ht : LocallySplit t) (hM : LocallyFiniteFree M)

/-- The actual ambient subobject recovered from a scheme section. -/
def atlasSubobject (p : X ⟶ LocallyFreeDualProjectiveAtlas.space M hM)
    (hp : p ≫ LocallyFreeDualProjectiveAtlas.projection M hM = 𝟙 X) : Subobject M :=
  Subobject.mk (DualAtlasSectionForwardLine.inclusion M hM p hp)

/-- Equal scheme sections give equal constructed ambient subobjects. -/
lemma atlasSubobject_congr {p q : X ⟶ LocallyFreeDualProjectiveAtlas.space M hM}
    (hp : p ≫ LocallyFreeDualProjectiveAtlas.projection M hM = 𝟙 X)
    (hq : q ≫ LocallyFreeDualProjectiveAtlas.projection M hM = 𝟙 X) (h : p = q) :
    atlasSubobject hM p hp = atlasSubobject hM q hq := by
  subst q
  rfl

/-- Equal actual atlas sections recover equal original ambient subobjects. -/
theorem subobject_eq_of_morphism_eq
    (h : morphism s hL hs hM = morphism t hN ht hM) :
    let _ := hs.mono s
    let _ := ht.mono t
    Subobject.mk s = Subobject.mk t := by
  let _ := hs.mono s
  let _ := ht.mono t
  change Subobject.mk s = Subobject.mk t
  rw [← forward_reverse_subobject s hL hs hM,
    ← forward_reverse_subobject t hN ht hM]
  exact atlasSubobject_congr hM _ _ h

/-- The atlas classifies original source lines up to inclusion-preserving isomorphism. -/
theorem morphism_eq_iff_sourceIso :
    morphism s hL hs hM = morphism t hN ht hM ↔
      ∃ a : L ≅ N, a.hom ≫ t = s := by
  constructor
  · intro h
    let _ := hs.mono s
    let _ := ht.mono t
    exact ⟨Subobject.isoOfMkEqMk s t
      (subobject_eq_of_morphism_eq s t hL hN hs ht hM h), by simp⟩
  · rintro ⟨a, ha⟩
    exact morphism_sourceIso s hL hs hM a t ha hN ht

end FLT.Mazur.LocallySplitLineAtlasSection
