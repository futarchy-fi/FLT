/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticStageRestriction
public import FLT.Mazur.PolygonInfinitesimalSystem

/-!
# The marked arithmetic polygon system over the original integral base

All arithmetic thickenings and their cyclic families assemble into compatible
systems. Every transition square is Cartesian, and specialization is a
natural transformation preserving the original labeled sections.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonArithmeticStages
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (A : Type u) [CommRing A] (π : A) (n : ℕ) (h : 2 ≤ n)

/-- The actual integral arithmetic coefficient thickenings and their inclusions. -/
def baseSystem : ℕ ⥤ Scheme.{u} := Functor.ofSequence (baseRestriction A π)

/-- The actual cyclic arithmetic families and their adjacent restrictions. -/
def stageSystem : ℕ ⥤ Scheme.{u} := Functor.ofSequence (fun m ↦ stageRestriction A π m n h)

/-- Every arithmetic stage retains its original coefficient spectrum. -/
def systemStructure : stageSystem A π n h ⟶ baseSystem A π :=
  NatTrans.ofSequence (fun m ↦ (family A π m n h).hom) (by
    intro m
    simpa only [stageSystem, baseSystem, Functor.ofSequence_obj,
      Functor.ofSequence_map_homOfLE_succ] using stageRestriction_base A π m n h)

/-- Each unchanged cyclic marking is a section of the entire arithmetic system. -/
def systemMarking (i : Fin n) : baseSystem A π ⟶ stageSystem A π n h :=
  NatTrans.ofSequence (fun m ↦ marking A π m n h i) (by
    intro m
    simpa only [stageSystem, baseSystem, Functor.ofSequence_obj,
      Functor.ofSequence_map_homOfLE_succ] using (marking_stageRestriction A π m n h i).symm)

/-- The actual marking satisfies the section equation on every stage. -/
theorem systemMarking_structure (i : Fin n) :
    systemMarking A π n h i ≫ systemStructure A π n h = 𝟙 (baseSystem A π) := by
  ext m
  exact marking_base A π m n h i

/-- Specialization of all original integral coefficient spectra. -/
def systemSpecializationBase : baseSystem A π ⟶ PolygonInfinitesimalStages.baseSystem A :=
  NatTrans.ofSequence (specializationBase A π) (by
    intro m
    simpa only [baseSystem, PolygonInfinitesimalStages.baseSystem, Functor.ofSequence_obj,
      Functor.ofSequence_map_homOfLE_succ] using baseRestriction_specialization A π m)

/-- The original universal integral families specialize naturally to the arithmetic system. -/
def systemSpecialization :
    stageSystem A π n h ⟶ PolygonInfinitesimalStages.stageSystem A n h :=
  NatTrans.ofSequence (fun m ↦ specializationFamily A π m n h) (by
    intro m
    simpa only [stageSystem, PolygonInfinitesimalStages.stageSystem, Functor.ofSequence_obj,
      Functor.ofSequence_map_homOfLE_succ] using stageRestriction_specialization A π m n h)

/-- System specialization retains the original integral coefficient maps. -/
theorem systemSpecialization_structure :
    systemSpecialization A π n h ≫ PolygonInfinitesimalStages.systemStructure A n h =
      systemStructure A π n h ≫ systemSpecializationBase A π := by
  ext m
  exact specializationFamily_base A π m n h

/-- Every arithmetic system transition is Cartesian, including nonadjacent orders. -/
theorem systemStructure_equifibered : (systemStructure A π n h).Equifibered := by
  suffices aux : ∀ a b (hab : a ≤ b),
      IsPullback ((stageSystem A π n h).map (homOfLE hab)) ((family A π a n h).hom)
        ((family A π b n h).hom) ((baseSystem A π).map (homOfLE hab)) from
    fun {_ _} f ↦ aux _ _ (leOfHom f)
  intro a b hab
  induction b, hab using Nat.le_induction with
  | base =>
    have he : homOfLE (show a ≤ a from le_rfl) = 𝟙 a := Subsingleton.elim _ _
    rw [he, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    change IsPullback (𝟙 (family A π a n h).left) (family A π a n h).hom
      (family A π a n h).hom (𝟙 (Spec (.of (Quotient A π a))))
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  | succ b hab ih =>
    have he : homOfLE (show a ≤ b + 1 by omega) =
        homOfLE hab ≫ homOfLE (Nat.le_succ b) := Subsingleton.elim _ _
    rw [he, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    have hb : IsPullback ((stageSystem A π n h).map (homOfLE (Nat.le_succ b)))
        (family A π b n h).hom (family A π (b + 1) n h).hom
        ((baseSystem A π).map (homOfLE (Nat.le_succ b))) := by
      simpa only [stageSystem, baseSystem, Functor.ofSequence_obj,
        Functor.ofSequence_map_homOfLE_succ] using stageRestriction_isPullback A π b n h
    exact ih.paste_horiz hb

/-- Pairwise disjoint labels persist at every order of the original arithmetic system. -/
theorem systemMarkings_pairwise (m : ℕ) : Pairwise (fun i j ↦
    Disjoint (Set.range ((systemMarking A π n h i).app m))
      (Set.range ((systemMarking A π n h j).app m))) :=
  markings_pairwise A π m n h

end FLT.Mazur.PolygonArithmeticStages
