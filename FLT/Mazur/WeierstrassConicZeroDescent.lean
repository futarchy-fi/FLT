/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXConicZeroParameters
public import FLT.Mazur.WeierstrassModificationXConicParameterHomExt
public import FLT.Mazur.BinaryOpenDescent

/-!
# Descent on the full zero-constant conic

Its two original parameter charts are disjoint and cover the entire conic.
Consequently arbitrary maps on the two charts glue with no extra compatibility.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {K : Type u} [Field K] (a c : K) (ha : IsUnit a) (hc : c = 0)
local notation "p₁" => (conicFirstParameterIso a c ha).inv ≫ conicFirstOpenImmersion a c
local notation "p₂" => (conicSecondParameterIso a c ha).inv ≫ conicSecondOpenImmersion a c

include hc in
/-- Both original parameter charts cover the full conic at the retained zero constant. -/
theorem conicZeroParameterCharts_cover (x : Spec (.of (ConicCoordinate a c))) :
    x ∈ Set.range p₁ ∨ x ∈ Set.range p₂ := by
  subst c
  have hx := Set.mem_univ x
  rw [← conicZeroParameters_cover a ha] at hx
  exact hx

include hc in
/-- Any pair of target maps agrees on the empty actual parameter intersection. -/
theorem conicZeroParameterMaps_compatible {Y : Scheme.{u}}
    (f g : Spec (.of (ConicParameterOpen c)) ⟶ Y) :
    pullback.fst p₁ p₂ ≫ f = pullback.snd p₁ p₂ ≫ g := by
  have hd : Disjoint (Set.range p₁) (Set.range p₂) := by
    subst c
    exact conicZeroParameters_disjoint a ha
  let _ := Scheme.isEmpty_pullback p₁ p₂ hd
  exact isInitialOfIsEmpty.hom_ext _ _

variable {Y : Scheme.{u}} (f g : Spec (.of (ConicParameterOpen c)) ⟶ Y)

/-- Glue the two original full parameters into a morphism from the complete conic. -/
@[irreducible] def conicZeroDesc : Spec (.of (ConicCoordinate a c)) ⟶ Y :=
  BinaryOpenDescent.desc (pullback.fst p₁ p₂) (pullback.snd p₁ p₂) p₁ p₂
    (IsPullback.of_hasPullback p₁ p₂) (conicZeroParameterCharts_cover a c ha hc) f g
    (conicZeroParameterMaps_compatible a c ha hc f g)

/-- The first full parameter recovers its original prescribed map. -/
@[reassoc] theorem conicZeroDesc_first : p₁ ≫ conicZeroDesc a c ha hc f g = f := by
  rw [conicZeroDesc]
  exact BinaryOpenDescent.inl_desc ..

/-- The second full parameter recovers its independently prescribed map. -/
@[reassoc] theorem conicZeroDesc_second : p₂ ≫ conicZeroDesc a c ha hc f g = g := by
  rw [conicZeroDesc]
  exact BinaryOpenDescent.inr_desc ..

/-- Full original parameter restrictions characterize the glued conic map uniquely. -/
theorem conicZeroDesc_unique (d : Spec (.of (ConicCoordinate a c)) ⟶ Y)
    (h₁ : p₁ ≫ d = f) (h₂ : p₂ ≫ d = g) : d = conicZeroDesc a c ha hc f g := by
  apply conicParameter_hom_ext a c ha
  · rw [h₁, conicZeroDesc_first]
  · rw [h₂, conicZeroDesc_second]

end FLT.Mazur.WeierstrassModificationX
