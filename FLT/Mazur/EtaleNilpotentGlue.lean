/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NilpotentClosedRestriction

/-!
# Gluing infinitesimal lifts into an etale scheme

Local lifts on any open cover agree on every overlap by formal unramifiedness.
Their glued morphism retains both sides of the original lifting square.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EtaleNilpotentGlue
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {T₀ T Y Z : Scheme} (i : T₀ ⟶ T) [IsClosedImmersion i]
  (hi : IsNilpotent i.ker) (g : Y ⟶ Z) [Etale g] (a : T₀ ⟶ Y) (v : T ⟶ Z)
  (𝒰 : T.OpenCover) (b : ∀ x, 𝒰.X x ⟶ Y)
  (ha : ∀ x, pullback.fst (𝒰.f x) i ≫ b x = pullback.snd _ _ ≫ a)
  (hv : ∀ x, b x ≫ g = 𝒰.f x ≫ v)

include hi ha hv in
/-- Formal uniqueness forces agreement on the whole scheme overlap. -/
theorem overlap (x y : 𝒰.I₀) :
    pullback.fst (𝒰.f x) (𝒰.f y) ≫ b x = pullback.snd _ _ ≫ b y := by
  let p := pullback.fst (𝒰.f x) (𝒰.f y)
  let q := pullback.snd (𝒰.f x) (𝒰.f y)
  let j := p ≫ 𝒰.f x
  let e := pullback.fst j i
  let t := pullback.snd j i
  have hj : j = q ≫ 𝒰.f y := pullback.condition
  let r₁ : pullback j i ⟶ pullback (𝒰.f x) i :=
    pullback.lift (e ≫ p) t (by simp only [Category.assoc]; exact pullback.condition)
  let r₂ : pullback j i ⟶ pullback (𝒰.f y) i :=
    pullback.lift (e ≫ q) t (by
      rw [Category.assoc, ← hj]
      exact pullback.condition)
  apply FormallyUnramified.hom_ext e
    (NilpotentClosedRestriction.pullback_nilpotent i hi j) g
  · calc
      e ≫ p ≫ b x = r₁ ≫ (pullback.fst (𝒰.f x) i ≫ b x) := by simp [r₁]
      _ = t ≫ a := by rw [ha x]; simp [r₁]
      _ = r₂ ≫ (pullback.fst (𝒰.f y) i ≫ b y) := by rw [ha y]; simp [r₂]
      _ = e ≫ q ≫ b y := by simp [r₂]
  · simp only [Category.assoc, hv]
    exact pullback.condition_assoc (f := 𝒰.f x) (g := 𝒰.f y) v

/-- Actual local lifts glue without any separate compatibility hypothesis. -/
def lift : T ⟶ Y := 𝒰.glueMorphisms b (overlap i hi g a v 𝒰 b ha hv)

/-- The glued map recovers each whole local lift. -/
@[reassoc]
theorem map_lift (x : 𝒰.I₀) : 𝒰.f x ≫ lift i hi g a v 𝒰 b ha hv = b x :=
  𝒰.ι_glueMorphisms _ _ x

/-- Gluing preserves the original lower-order arrow. -/
@[reassoc]
theorem inclusion_lift : i ≫ lift i hi g a v 𝒰 b ha hv = a := by
  apply Scheme.Cover.hom_ext (𝒰.pullback₂ i)
  intro x
  change pullback.snd (𝒰.f x) i ≫ (i ≫ _) = pullback.snd _ _ ≫ a
  rw [← pullback.condition_assoc, map_lift, ha]

/-- Gluing preserves the original coefficient morphism. -/
@[reassoc]
theorem lift_base : lift i hi g a v 𝒰 b ha hv ≫ g = v := by
  apply 𝒰.hom_ext
  intro x
  rw [← Category.assoc, map_lift, hv]

include hi ha hv in
/-- A locally solvable etale lifting square has one unique whole scheme lift. -/
theorem existsUnique_lift : ∃! c : T ⟶ Y, i ≫ c = a ∧ c ≫ g = v := by
  refine ⟨lift i hi g a v 𝒰 b ha hv,
    ⟨inclusion_lift i hi g a v 𝒰 b ha hv, lift_base i hi g a v 𝒰 b ha hv⟩, ?_⟩
  intro c hc
  exact FormallyUnramified.hom_ext i hi g
    (hc.1.trans (inclusion_lift i hi g a v 𝒰 b ha hv).symm)
    (hc.2.trans (lift_base i hi g a v 𝒰 b ha hv).symm)

end FLT.Mazur.EtaleNilpotentGlue
