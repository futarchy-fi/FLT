/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FaithfullyFlatTowerReflection
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Flatness detected by jointly surjective flat source maps

At a lifted point a flat map of local stalk rings is faithfully flat.
Reflection through this ring extension detects flatness of the original
stalk map. No quasi-compactness or finiteness assumption on the family is used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.SchemeFlatFamilyReflection
variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Flat source maps detect flatness at their image points. -/
theorem stalkMap_flat_of_comp {Y : Scheme.{u}} (p : Y ⟶ X)
    [Flat p] [Flat (p ≫ f)] (y : Y) : (f.stalkMap (p y)).hom.Flat := by
  let : Algebra (X.presheaf.stalk (p y)) (Y.presheaf.stalk y) :=
    (p.stalkMap y).hom.toAlgebra
  let : Module.Flat (X.presheaf.stalk (p y)) (Y.presheaf.stalk y) := Flat.stalkMap p y
  let : IsLocalHom (algebraMap (X.presheaf.stalk (p y)) (Y.presheaf.stalk y)) :=
    p.toLRSHom.prop y
  have hb : (p.stalkMap y).hom.FaithfullyFlat :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  apply FaithfullyFlatTowerReflection.ringHom_flat_of_comp _ _ hb
  simpa only [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp] using
    Flat.stalkMap (p ≫ f) y

/-- A jointly surjective flat source family detects flatness of the original morphism. -/
theorem flat_of_family {ι : Type*} (Y : ι → Scheme.{u}) (p : ∀ i, Y i ⟶ X)
    [∀ i, Flat (p i)] (hp : ∀ x : X, ∃ i, ∃ y : Y i, p i y = x)
    (h : ∀ i, Flat (p i ≫ f)) : Flat f := by
  apply Flat.of_stalkMap
  intro x
  obtain ⟨i, y, rfl⟩ := hp x
  let _ := h i
  exact stalkMap_flat_of_comp f (p i) y

/-- An arbitrary small fppf source cover detects flatness. -/
theorem flat_of_fppf_cover (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage X)
    (h : ∀ i, Flat (𝒰.f i ≫ f)) : Flat f := by
  let V : X.Cover (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) := 𝒰
  let _ (i : 𝒰.I₀) : Flat (𝒰.f i) :=
    (Scheme.Cover.map_prop (P := @Flat ⊓ @LocallyOfFinitePresentation) 𝒰 i).1
  exact flat_of_family f 𝒰.X 𝒰.f (fun x ↦ V.exists_eq x) h

end FLT.Mazur.SchemeFlatFamilyReflection
