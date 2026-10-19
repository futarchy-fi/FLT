/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap

/-!
# Global morphisms from rational maps with full domain

The maximal partial map glues the actual regular representatives. When its
domain is the whole scheme, the open inclusion is an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.WholeDomainRationalMap

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {X Y : Scheme.{u}} [IsReduced X] [Y.IsSeparated]
  (f : X.RationalMap Y) (hf : f.domain = ⊤)

include hf in
omit [IsReduced X] [Y.IsSeparated] in
/-- Full rational domain makes its inclusion an isomorphism. -/
theorem domain_isIso : IsIso f.domain.ι := by
  rw [hf]
  exact inferInstanceAs (IsIso X.topIso.hom)

/-- The global morphism glued from the rational map's regular representatives. -/
def globalHom : X ⟶ Y :=
  let _ := domain_isIso f hf
  inv f.domain.ι ≫ f.toPartialMap.hom

/-- The global morphism retains the maximal regular representative. -/
@[reassoc] theorem inclusion_globalHom : f.domain.ι ≫ globalHom f hf = f.toPartialMap.hom := by
  let _ := domain_isIso f hf
  exact IsIso.hom_inv_id_assoc _ _

/-- The global morphism represents exactly the initial rational map. -/
theorem globalHom_toRationalMap : (globalHom f hf).toRationalMap = f := by
  apply Eq.trans _ f.toRationalMap_toPartialMap
  apply Scheme.PartialMap.toRationalMap_eq_iff.mpr
  refine ⟨f.domain, f.dense_domain, le_top, le_rfl, ?_⟩
  change X.homOfLE (U := f.domain) (V := ⊤) le_top ≫
    ((⊤ : X.Opens).ι ≫ globalHom f hf) =
    X.homOfLE (U := f.domain) (V := f.domain) le_rfl ≫ f.toPartialMap.hom
  rw [← Category.assoc, Scheme.homOfLE_ι, Scheme.homOfLE_rfl, Category.id_comp]
  exact inclusion_globalHom f hf

/-- Each original regular representative is the restriction of the global morphism. -/
@[reassoc] theorem representative_globalHom (g : X.PartialMap Y)
    (hg : g.toRationalMap = f) : g.domain.ι ≫ globalHom f hf = g.hom := by
  subst f
  have hr := g.toPartialMap_toRationalMap_restrict
  change X.homOfLE (U := g.domain) (V := g.toRationalMap.domain)
    g.le_domain_toRationalMap ≫ g.toRationalMap.toPartialMap.hom = g.hom at hr
  rw [← inclusion_globalHom _ hf, ← Category.assoc, Scheme.homOfLE_ι] at hr
  exact hr

/-- Morphisms to a separated scheme are determined by their rational maps. -/
theorem hom_ext (a b : X ⟶ Y) (h : a.toRationalMap = b.toRationalMap) : a = b := by
  have he := (Scheme.PartialMap.equiv_iff_of_isSeparated_of_le
    (S := Limits.terminal Scheme) (f := a.toPartialMap) (g := b.toPartialMap)
    (W := ⊤) dense_univ le_rfl le_rfl).mp
      (Scheme.PartialMap.toRationalMap_eq_iff.mp h)
  change X.homOfLE le_rfl ≫ (X.topIso.hom ≫ a) =
    X.homOfLE le_rfl ≫ (X.topIso.hom ≫ b) at he
  rw [Scheme.homOfLE_rfl, Category.id_comp, Category.id_comp] at he
  exact (cancel_epi X.topIso.hom).mp he

/-- The global extension is unique among all morphisms representing the given rational map. -/
theorem globalHom_unique (a : X ⟶ Y) (ha : a.toRationalMap = f) : a = globalHom f hf :=
  hom_ext a _ (ha.trans (globalHom_toRationalMap f hf).symm)

end FLT.Mazur.WholeDomainRationalMap
