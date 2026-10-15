/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticSectionRings
public import FLT.Mazur.SectionGradedLineRingCoherence

/-!
# Functoriality of the actual polygon boundary section rings

All stage maps satisfy identity and composition. The resulting functor has
the same maps as the inverse system previously built from adjacent stages.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (A : Type) [CommRing A] (π : A) (n : ℕ) (h : 2 ≤ n)

/-- The actual boundary section-ring transition for an identity fixes every section. -/
theorem boundarySectionsMap_id (a : ℕ) :
    boundarySectionsMap A π n h (𝟙 a) = RingHom.id _ := by
  change SectionGradedLinePullback.ringHom _ (boundaryLineSystemIso A π n h (𝟙 a)) = _
  rw [boundaryLineSystemIso_id]
  exact SectionGradedLinePullback.ringHom_id_eq _ _ _

/-- The actual boundary section-ring transitions compose on all homogeneous degrees. -/
theorem boundarySectionsMap_comp {a b c : ℕ} (f : a ⟶ b) (g : b ⟶ c) :
    boundarySectionsMap A π n h (f ≫ g) =
      (boundarySectionsMap A π n h f).comp (boundarySectionsMap A π n h g) :=
  SectionGradedLinePullback.ringHom_comp_eq _ _ _ ((stageSystem A π n h).map_comp f g)
    (boundaryLineSystemIso A π n h g) (boundaryLineSystemIso A π n h f)
    (boundaryLineSystemIso A π n h (f ≫ g)) (boundaryLineSystemIso_comp A π n h f g)

/-- The inverse functor using the specified boundary-line map on every stage morphism. -/
def boundarySectionRingFunctor : ℕᵒᵖ ⥤ CommRingCat where
  obj a := CommRingCat.of (boundaryGradedSections A π n h a.unop)
  map f := CommRingCat.ofHom (boundarySectionsMap A π n h f.unop)
  map_id a := by
    change CommRingCat.ofHom (boundarySectionsMap A π n h (𝟙 a.unop)) = _
    rw [boundarySectionsMap_id]
    rfl
  map_comp f g := by
    change CommRingCat.ofHom (boundarySectionsMap A π n h (g.unop ≫ f.unop)) = _
    rw [boundarySectionsMap_comp]
    rfl

/-- The identity on every ring compares the adjacent construction with all actual stage maps. -/
def boundarySectionRingSystemComparison :
    boundarySectionRingSystem A π n h ⟶ boundarySectionRingFunctor A π n h :=
  NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (by
    intro a
    simp only [Category.comp_id, Category.id_comp]
    exact Functor.ofOpSequence_map_homOfLE_succ _ a)

/-- Every map of the adjacent inverse system is the original boundary-line section map. -/
theorem boundarySectionRingSystem_map {a b : ℕᵒᵖ} (f : a ⟶ b) :
    (boundarySectionRingSystem A π n h).map f =
      CommRingCat.ofHom (boundarySectionsMap A π n h f.unop) := by
  have hh := (boundarySectionRingSystemComparison A π n h).naturality f
  change _ ≫ 𝟙 _ = 𝟙 _ ≫ _ at hh
  rw [Category.comp_id, Category.id_comp] at hh
  exact hh

/-- The previous adjacent inverse system and the full-map functor are canonically isomorphic. -/
def boundarySectionRingSystemIso :
    boundarySectionRingSystem A π n h ≅ boundarySectionRingFunctor A π n h :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro a b f
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact boundarySectionRingSystem_map A π n h f)

end FLT.Mazur.PolygonArithmeticStages
