/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AuxiliaryLevelFaithfulOpen

/-!
# The universal property of the faithful-marking open

Faithfulness means injectivity after every nonempty test scheme, not merely
injectivity on the original base's global sections. The explicit open scheme
represents exactly this condition. The converse uses actual scheme pullbacks
of the closed kernel equations, so it also detects residue-field coincidences.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonObj

namespace FLT.Mazur.AuxiliaryLevel

variable {S : Scheme} (E : Over S) [GrpObj E] [IsSeparated E.hom]
  (A : Type) [Group A] [Fintype A]

/-- The marking remains injective after every nonempty test scheme. -/
def UniversallyFaithful {U : Over S} (f : U ⟶ homScheme E A) : Prop :=
  ∀ (V : Over S) (g : V ⟶ U), Nonempty V.left →
    Function.Injective (markingOf E A (g ≫ f))

/-- Maps into the faithful open give universally faithful markings. -/
theorem faithfulInclusion_universallyFaithful {U : Over S}
    (f : U ⟶ faithfulScheme E A) :
    UniversallyFaithful E A (f ≫ faithfulInclusion E A) := by
  intro V g hV
  let _ := hV
  simpa only [Category.assoc] using faithful_marking_injective E A (g ≫ f)

/-- Universal injectivity forces the image to avoid every nontrivial kernel equation. -/
theorem universallyFaithful_range {U : Over S} (f : U ⟶ homScheme E A)
    (hf : UniversallyFaithful E A f) : Set.range f.left ⊆ faithfulOpen E A := by
  rintro _ ⟨x, rfl⟩
  change f.left x ∈ faithfulOpen E A
  apply (mem_faithfulOpen E A _).mpr
  intro a ha
  rintro ⟨y, hy⟩
  let V : Over S := Over.mk (pullback.fst f.left (kernelInclusion E a).left ≫ U.hom)
  let g : V ⟶ U := Over.homMk (pullback.fst f.left (kernelInclusion E a).left) rfl
  let k : V ⟶ kernelScheme E a := Over.homMk (pullback.snd f.left
    (kernelInclusion E a).left) (by
      rw [← (kernelInclusion E a).w, ← Category.assoc, ← pullback.condition,
        Category.assoc, f.w]
      rfl)
  have h : g ≫ f = k ≫ kernelInclusion E a := by
    apply Over.OverMorphism.ext
    exact pullback.condition
  obtain ⟨z, _, _⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
  have hV : Nonempty V.left := ⟨z⟩
  have hz : markingOf E A (g ≫ f) a = 1 := by
    change (g ≫ f) ≫ value E A a = 1
    rw [h, Category.assoc, kernelInclusion_value, MonObj.comp_one]
  exact ha (hf V g hV (hz.trans (map_one (markingOf E A (g ≫ f))).symm))

/-- The canonical factorization through the constructed faithful open. -/
def faithfulLift {U : Over S} (f : U ⟶ homScheme E A)
    (hf : UniversallyFaithful E A f) : U ⟶ faithfulScheme E A := by
  change U ⟶ Over.mk ((faithfulOpen E A).ι ≫ (homScheme E A).hom)
  refine Over.homMk
    (IsOpenImmersion.lift (faithfulOpen E A).ι f.left (by
      rintro _ ⟨x, rfl⟩
      exact ⟨⟨f.left x, universallyFaithful_range E A f hf ⟨x, rfl⟩⟩, rfl⟩)) (by
        change _ ≫ (faithfulOpen E A).ι ≫ (homScheme E A).hom = U.hom
        rw [IsOpenImmersion.lift_fac_assoc, f.w])

/-- The factorization preserves every original marked section. -/
@[reassoc (attr := simp)] theorem faithfulLift_inclusion {U : Over S}
    (f : U ⟶ homScheme E A) (hf : UniversallyFaithful E A f) :
    faithfulLift E A f hf ≫ faithfulInclusion E A = f := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac (faithfulOpen E A).ι f.left _

/-- Factorization through the open is precisely universal faithfulness. -/
theorem universallyFaithful_iff_existsUnique {U : Over S} (f : U ⟶ homScheme E A) :
    UniversallyFaithful E A f ↔
      ∃! g : U ⟶ faithfulScheme E A, g ≫ faithfulInclusion E A = f := by
  constructor
  · intro hf
    refine ⟨faithfulLift E A f hf, faithfulLift_inclusion E A f hf, ?_⟩
    intro g hg
    apply Over.OverMorphism.ext
    apply (cancel_mono (faithfulOpen E A).ι).mp
    exact congrArg Over.Hom.left (hg.trans (faithfulLift_inclusion E A f hf).symm)
  · rintro ⟨g, rfl, _⟩
    exact faithfulInclusion_universallyFaithful E A g

/-- The faithful open represents universally injective finite group markings. -/
def faithfulRepresentation (U : Over S) :
    (U ⟶ faithfulScheme E A) ≃ {f : U ⟶ homScheme E A // UniversallyFaithful E A f} where
  toFun f := ⟨f ≫ faithfulInclusion E A, faithfulInclusion_universallyFaithful E A f⟩
  invFun f := faithfulLift E A f.val f.property
  left_inv f := by
    apply Over.OverMorphism.ext
    apply (cancel_mono (faithfulOpen E A).ι).mp
    exact congrArg Over.Hom.left (faithfulLift_inclusion E A _ _)
  right_inv f := Subtype.ext (faithfulLift_inclusion E A _ _)

end FLT.Mazur.AuxiliaryLevel
