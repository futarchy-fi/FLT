/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalStageRestriction
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# The compatible marked infinitesimal polygon system

Successive actual restrictions construct functors on the natural-number order.
Their structure morphisms and markings are natural transformations. Every
transition square is cartesian, by pasting the proved adjacent-stage squares.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (R : Type u) [CommRing R] (n : ℕ) (h : 2 ≤ n)

/-- The system of actual truncated coefficient spectra. -/
def baseSystem : ℕ ⥤ Scheme.{u} :=
  Functor.ofSequence (baseRestriction R)

/-- The system of actual cyclic infinitesimal families and their restrictions. -/
def stageSystem : ℕ ⥤ Scheme.{u} :=
  Functor.ofSequence (fun m ↦ stageRestriction R m n h)

/-- The compatible structure maps of the complete infinitesimal system. -/
def systemStructure : stageSystem R n h ⟶ baseSystem R :=
  NatTrans.ofSequence (fun m ↦ (family R m n h).hom) (by
    intro m
    simpa only [stageSystem, baseSystem, Functor.ofSequence_obj,
      Functor.ofSequence_map_homOfLE_succ] using
      stageRestriction_base R m n h)

/-- The specified marking on each stage is compatible with every system transition. -/
def systemMarking (i : Fin n) : baseSystem R ⟶ stageSystem R n h :=
  NatTrans.ofSequence (fun m ↦ marking R m n h i) (by
    intro m
    simpa only [stageSystem, baseSystem, Functor.ofSequence_obj,
      Functor.ofSequence_map_homOfLE_succ] using
      (marking_stageRestriction R m n h i).symm)

/-- Every marking remains a section of the entire infinitesimal system. -/
theorem systemMarking_structure (i : Fin n) :
    systemMarking R n h i ≫ systemStructure R n h = 𝟙 (baseSystem R) := by
  ext m
  exact marking_base R m n h i

/-- Every transition of the assembled system is the actual coefficient pullback. -/
theorem systemStructure_equifibered : (systemStructure R n h).Equifibered := by
  suffices aux : ∀ a b (hab : a ≤ b),
      IsPullback ((stageSystem R n h).map (homOfLE hab)) ((family R a n h).hom)
        ((family R b n h).hom) ((baseSystem R).map (homOfLE hab)) from
    fun {_ _} f ↦ aux _ _ (leOfHom f)
  intro a b hab
  induction b, hab using Nat.le_induction with
  | base =>
    have he : homOfLE (show a ≤ a from le_rfl) = 𝟙 a := Subsingleton.elim _ _
    rw [he, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    change IsPullback (𝟙 (family R a n h).left) (family R a n h).hom
      (family R a n h).hom (𝟙 (Spec (.of (Ring R a))))
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  | succ b hab ih =>
    have he : homOfLE (show a ≤ b + 1 by omega) =
        homOfLE hab ≫ homOfLE (Nat.le_succ b) := Subsingleton.elim _ _
    rw [he, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    have hb : IsPullback ((stageSystem R n h).map (homOfLE (Nat.le_succ b)))
        (family R b n h).hom (family R (b + 1) n h).hom
        ((baseSystem R).map (homOfLE (Nat.le_succ b))) := by
      simpa only [stageSystem, baseSystem, Functor.ofSequence_obj,
      Functor.ofSequence_map_homOfLE_succ] using
        stageRestriction_isPullback R b n h
    exact ih.paste_horiz hb

/-- The chosen markings remain pairwise disjoint at every finite order of the system. -/
theorem systemMarkings_pairwise (m : ℕ) :
    Pairwise (fun i j ↦ Disjoint (Set.range ((systemMarking R n h i).app m))
      (Set.range ((systemMarking R n h j).app m))) :=
  markings_pairwise R m n h

end FLT.Mazur.PolygonInfinitesimalStages
