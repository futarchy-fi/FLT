/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonStageCoefficientTransitions

/-!
# Coefficient comparison of the entire marked stage systems

The adjacent squares assemble into natural transformations on every stage
transition, preserving structure maps, the complete base, and all markings.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) (h : 2 ≤ n)

/-- Coefficient change on the original system of truncated bases. -/
def coefficientBaseSystem : baseSystem S ⟶ baseSystem R :=
  NatTrans.ofSequence (stageCoefficientBase f) (by
    intro m
    simpa only [baseSystem, Functor.ofSequence_map_homOfLE_succ] using
      stageCoefficientBase_restriction f m)

/-- Coefficient change on the original system of whole marked families. -/
def coefficientFamilySystem : stageSystem S n h ⟶ stageSystem R n h :=
  NatTrans.ofSequence (fun m ↦ stageCoefficientFamily f m n h) (by
    intro m
    simpa only [stageSystem, Functor.ofSequence_map_homOfLE_succ] using
      stageCoefficientFamily_restriction f m n h)

/-- All original structural maps commute with the system comparison. -/
theorem coefficientFamilySystem_structure :
    coefficientFamilySystem f n h ≫ systemStructure R n h =
      systemStructure S n h ≫ coefficientBaseSystem f := by
  ext m
  exact (stageCoefficientFamily_isPullback f m n h).w

/-- Each labeled marking is retained throughout the system. -/
theorem coefficientFamilySystem_marking (i : Fin n) :
    systemMarking S n h i ≫ coefficientFamilySystem f n h =
      coefficientBaseSystem f ≫ systemMarking R n h i := by
  ext m
  exact marking_stageCoefficientFamily f m n h i

/-- Every original transition commutes with the coefficient family comparison. -/
@[reassoc] theorem stageCoefficientFamily_naturality {a b : ℕ} (g : a ⟶ b) :
    (stageSystem S n h).map g ≫ stageCoefficientFamily f b n h =
      stageCoefficientFamily f a n h ≫ (stageSystem R n h).map g :=
  (coefficientFamilySystem f n h).naturality g

end FLT.Mazur.PolygonInfinitesimalStages
