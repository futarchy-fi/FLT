/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineFreeSectionLineComparison
public import FLT.Mazur.SectionLinePointOverlapEquality

/-!
# Affine line subobjects recover their projective points

Full faithfulness of affine tilde reflects containment of section submodules
from containment of their actual sheaf inclusions. Thus equality of the
original free-sheaf subobjects is exactly equality of projective points,
independently of the coordinate used to normalize the line.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.AffineFreeSheafCoordinates
open AffineModuleGlobalSections NormalizedSectionLine
variable (X : Scheme.{u}) [IsAffine X] {ι : Type u} [Finite ι]

/-- Actual sheaf subobject containment reflects containment of the original section lines. -/
lemma sectionLine_val_le_of_subobject_le (i j : ι)
    (L : Chart Γ(X, ⊤) ι i) (N : Chart Γ(X, ⊤) ι j)
    (h : Subobject.mk (sectionLineInclusion X i L) ≤
      Subobject.mk (sectionLineInclusion X j N)) : L.val ≤ N.val := by
  let b := Subobject.ofMkLEMk (sectionLineInclusion X i L) (sectionLineInclusion X j N) h
  have hb : b ≫ (affineTilde X).map (ModuleCat.ofHom N.val.subtype) =
      (affineTilde X).map (ModuleCat.ofHom L.val.subtype) := by
    apply (cancel_mono (vectorFreeIso X ι).hom).mp
    exact Subobject.ofMkLEMk_comp h
  let c := (affineTilde X).preimage b
  have hc : c ≫ ModuleCat.ofHom N.val.subtype = ModuleCat.ofHom L.val.subtype := by
    apply (affineTilde X).map_injective
    rw [Functor.map_comp, Functor.map_preimage]
    exact hb
  intro v hv
  have he := ConcreteCategory.congr_hom hc (⟨v, hv⟩ : L.val)
  change (c (⟨v, hv⟩ : L.val)).val = v at he
  exact he ▸ (c (⟨v, hv⟩ : L.val)).property

/-- The actual free-sheaf subobject determines the section submodule in every chart. -/
lemma sectionLine_subobject_eq_iff (i j : ι)
    (L : Chart Γ(X, ⊤) ι i) (N : Chart Γ(X, ⊤) ι j) :
    Subobject.mk (sectionLineInclusion X i L) =
      Subobject.mk (sectionLineInclusion X j N) ↔ L.val = N.val := by
  constructor
  · intro h
    exact le_antisymm (sectionLine_val_le_of_subobject_le X i j L N h.le)
      (sectionLine_val_le_of_subobject_le X j i N L h.ge)
  · intro h
    let e := (affineTilde X).mapIso
      (LinearEquiv.ofEq L.val N.val h).toModuleIso
    apply Subobject.mk_eq_mk_of_comm _ _ e
    dsimp only [e, Functor.mapIso_hom, sectionLineInclusion]
    rw [← Category.assoc, ← Functor.map_comp]
    congr 2

/-- Equality of actual affine line subobjects is precisely equality of projective points. -/
lemma sectionLine_subobject_eq_iff_point (i j : ι)
    (L : Chart Γ(X, ⊤) ι i) (N : Chart Γ(X, ⊤) ι j) :
    Subobject.mk (sectionLineInclusion X i L) =
      Subobject.mk (sectionLineInclusion X j N) ↔
    ProjectiveSpace.sectionLinePoint Γ(X, ⊤) ι (.id _) i L =
      ProjectiveSpace.sectionLinePoint Γ(X, ⊤) ι (.id _) j N := by
  rw [sectionLine_subobject_eq_iff, ProjectiveSpace.sectionLinePoint_eq_iff]

end FLT.Mazur.AffineFreeSheafCoordinates
