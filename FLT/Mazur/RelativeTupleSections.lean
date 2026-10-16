/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeDistinctEtale
public import FLT.Mazur.UnramifiedSectionImmersion

/-!
# Universal sections of the full relation over its ordered-point scheme

Base change the entire original source to its distinct-tuple scheme. Every
coordinate gives a clopen section of this full pullback, including its scheme
structure. Their union need not exhaust the pullback away from a complete fiber.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  (I : Type) [Fintype I]

/-- The entire original source pulled back to the ordered-point scheme. -/
def framedSource : Scheme := pullback E.hom (distinctScheme E I).hom

/-- The unchanged projection from the full pullback to its frame. -/
def framedProjection : framedSource E I ⟶ (distinctScheme E I).left :=
  pullback.snd E.hom (distinctScheme E I).hom

instance framedProjection_etale : Etale (framedProjection E I) :=
  inferInstanceAs (Etale (pullback.snd E.hom (distinctScheme E I).hom))

instance framedProjection_separated : IsSeparated (framedProjection E I) :=
  inferInstanceAs (IsSeparated (pullback.snd E.hom (distinctScheme E I).hom))

/-- A universal coordinate as a section of the full base-changed original source. -/
def framedSection (i : I) : (distinctScheme E I).left ⟶ framedSource E I :=
  pullback.lift (distinctCoordinate E I i).left (𝟙 _) (by
    rw [Category.id_comp]
    exact (distinctCoordinate E I i).w)

omit [Etale E.hom] in
/-- Each universal coordinate lies over the same original frame. -/
@[reassoc (attr := simp)] theorem framedSection_projection (i : I) :
    framedSection E I i ≫ framedProjection E I = 𝟙 _ := pullback.lift_snd _ _ _

omit [Etale E.hom] in
/-- The section retains the original coordinate map into the full source. -/
@[reassoc (attr := simp)] theorem framedSection_original (i : I) :
    framedSection E I i ≫ pullback.fst E.hom (distinctScheme E I).hom =
      (distinctCoordinate E I i).left := pullback.lift_fst _ _ _

instance framedSection_open (i : I) : IsOpenImmersion (framedSection E I i) :=
  UnramifiedSectionImmersion.isOpenImmersion (framedProjection E I) _
    (framedSection_projection E I i)

instance framedSection_closed (i : I) : IsClosedImmersion (framedSection E I i) :=
  UnramifiedSectionImmersion.isClosedImmersion (framedProjection E I) _
    (framedSection_projection E I i)

/-- The locus actually enumerated by the universal coordinates. -/
def enumeratedOpen : (framedSource E I).Opens :=
  ⟨⋃ i : I, Set.range (framedSection E I i),
    isOpen_iUnion fun i ↦ (framedSection E I i).isOpenEmbedding.isOpen_range⟩

/-- The enumerated locus is closed as well as open, without finiteness of the source. -/
theorem enumeratedOpen_isClosed :
    IsClosed (enumeratedOpen E I : Set (framedSource E I)) :=
  isClosed_iUnion_of_finite fun i ↦ (framedSection E I i).isClosedEmbedding.isClosed_range

/-- Membership records an actual coordinate section, not merely equal original images. -/
theorem mem_enumeratedOpen (x : framedSource E I) :
    x ∈ enumeratedOpen E I ↔ ∃ i, framedSection E I i (framedProjection E I x) = x := by
  simp only [enumeratedOpen, TopologicalSpace.Opens.mem_mk, Set.mem_iUnion]
  constructor
  · rintro ⟨i, y, rfl⟩
    refine ⟨i, ?_⟩
    have h := congrArg (fun m : (distinctScheme E I).left ⟶ _ ↦ m y)
      (framedSection_projection E I i)
    exact congrArg (framedSection E I i) h
  · rintro ⟨i, hi⟩
    exact ⟨i, framedProjection E I x, hi⟩

end FLT.Mazur.RelativeOrderedTuples
