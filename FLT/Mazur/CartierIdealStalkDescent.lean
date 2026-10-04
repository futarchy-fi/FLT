/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AnnihilatorStalk
public import FLT.Mazur.AffinePullbackIdeal
public import FLT.Mazur.CartierCharts
public import FLT.Mazur.LocalCartierGeneratorDescent

/-!
# Regular generators of the actual Cartier ideal stalks

Comap of ideal sheaves extends their stalk ideals by the actual stalk map.
Flat surjective pullback therefore detects regular principal ideal stalks.
Spreading these generators to Cartier neighborhoods is a separate obligation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open AnnihilatorSubsheaf
variable {X Y : Scheme.{u}}

/-- Pullback of ideal sheaves extends the actual ideal stalk. -/
lemma stalkIdeal_comap (I : Y.IdealSheafData) (f : X ⟶ Y) (x : X) :
    stalkIdeal (I.comap f) x = (stalkIdeal I (f x)).map (f.stalkMap x).hom := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, _⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x))
      TopologicalSpace.isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxV (f ⁻¹ᵁ V).isOpen
  rw [stalkIdeal_eq_map _ x ⟨U, hU⟩ hxU,
    stalkIdeal_eq_map I (f x) ⟨V, hV⟩ hxV,
    Scheme.IdealSheafData.ideal_comap I f ⟨V, hV⟩ ⟨U, hU⟩ hUV,
    Ideal.map_map, Ideal.map_map]
  congr 1
  ext a
  change X.presheaf.germ U x hxU (f.appLE V U hUV a) =
    f.stalkMap x (Y.presheaf.germ V (f x) hxV a)
  rw [Scheme.Hom.germ_stalkMap_apply]
  exact X.presheaf.germ_res_apply (homOfLE hUV) x hxU (f.app V a)

/-- A Cartier chart gives a regular generator of the actual ideal stalk. -/
lemma EffectiveCartier.stalk_generator {I : X.IdealSheafData} (hI : EffectiveCartier I)
    (x : X) : ∃ a : X.presheaf.stalk x, IsRegular a ∧ stalkIdeal I x = Ideal.span {a} := by
  obtain ⟨U, hxU, a, ha, hIa⟩ := hI x
  let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  let := U.2.isLocalization_stalk ⟨x, hxU⟩
  let : Module.Flat Γ(X, U) (X.presheaf.stalk x) :=
    IsLocalization.flat (X.presheaf.stalk x) (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  have hr : IsRegular (algebraMap Γ(X, U) (X.presheaf.stalk x) a) := by
    rw [← isLeftRegular_iff_isRegular]
    simpa only [IsSMulRegular, IsLeftRegular, Algebra.smul_def] using
      (Module.Flat.isSMulRegular_of_isRegular (M := X.presheaf.stalk x) ha)
  refine ⟨X.presheaf.germ U.1 x hxU a, hr, ?_⟩
  rw [stalkIdeal_eq_map I x U hxU, hIa, Ideal.map_span, Set.image_singleton]

/-- A flat morphism descends a Cartier stalk generator at each point in its image. -/
theorem stalk_generator_of_flat_comap (I : Y.IdealSheafData) (f : X ⟶ Y) [Flat f]
    (hI : EffectiveCartier (I.comap f)) (x : X) :
    ∃ a : Y.presheaf.stalk (f x), IsRegular a ∧ stalkIdeal I (f x) = Ideal.span {a} := by
  let : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := Flat.stalkMap f x
  let : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    f.toLRSHom.prop x
  obtain ⟨b, hb, hIb⟩ := hI.stalk_generator x
  rw [stalkIdeal_comap] at hIb
  exact exists_regular_generator_of_flat_local (stalkIdeal I (f x)) b hb hIb

/-- A flat surjective Cartier pullback gives regular principal stalks everywhere. -/
theorem stalk_generators_of_flat_surjective_comap (I : Y.IdealSheafData)
    (f : X ⟶ Y) [Flat f] [Surjective f] (hI : EffectiveCartier (I.comap f)) (y : Y) :
    ∃ a : Y.presheaf.stalk y, IsRegular a ∧ stalkIdeal I y = Ideal.span {a} := by
  obtain ⟨x, rfl⟩ := f.surjective y
  exact stalk_generator_of_flat_comap I f hI x

end FLT.Mazur.FCurve
