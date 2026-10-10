/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OpenImmersionImageUnion
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Covers of intersections by prescribed common open subschemes

A common family whose images exhaust the chart intersection gives an
actual cover of the pullback, and hence detects equality of morphisms.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur

universe u v

variable {X U V : Scheme.{u}} (f : U ⟶ X) (g : V ⟶ X)
  {ι : Type v} {W : ι → Scheme.{u}}
  (a : ∀ i, W i ⟶ U) (b : ∀ i, W i ⟶ V)
  (h : ∀ i, a i ≫ f = b i ≫ g)

/-- Each prescribed common open maps into the actual intersection. -/
def openImmersionCommonMap (i : ι) : W i ⟶ pullback f g :=
  pullback.lift (a i) (b i) (h i)

/-- The common map retains the first literal embedding. -/
@[reassoc (attr := simp)] theorem openImmersionCommonMap_fst (i : ι) :
    openImmersionCommonMap f g a b h i ≫ pullback.fst f g = a i :=
  pullback.lift_fst _ _ _

/-- The common map retains the second literal embedding. -/
@[reassoc (attr := simp)] theorem openImmersionCommonMap_snd (i : ι) :
    openImmersionCommonMap f g a b h i ≫ pullback.snd f g = b i :=
  pullback.lift_snd _ _ _

variable [IsOpenImmersion g] [∀ i, IsOpenImmersion (a i)]

/-- The common maps are open immersions into the full intersection. -/
instance openImmersionCommonMap_isOpenImmersion (i : ι) :
    IsOpenImmersion (openImmersionCommonMap f g a b h i) := by
  have : IsOpenImmersion (openImmersionCommonMap f g a b h i ≫ pullback.fst f g) := by
    rw [openImmersionCommonMap_fst]
    infer_instance
  exact IsOpenImmersion.of_comp _ (pullback.fst f g)

variable (hc : (⨆ i, (a i).opensRange) = f ⁻¹ᵁ g.opensRange)

/-- Exhaustive common images cover the actual scheme pullback. -/
def openImmersionCommonCover : (pullback f g).OpenCover where
  I₀ := ι
  X := W
  f := openImmersionCommonMap f g a b h
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro z
    have hz : pullback.fst f g z ∈ f ⁻¹ᵁ g.opensRange := by
      change f (pullback.fst f g z) ∈ Set.range g
      refine ⟨pullback.snd f g z, ?_⟩
      exact (congrArg (fun k : pullback f g ⟶ X ↦ k z) (pullback.condition (f := f) (g := g))).symm
    rw [← hc] at hz
    obtain ⟨i, w, hw⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
    refine ⟨i, w, ?_⟩
    apply (pullback.fst f g).isOpenEmbedding.injective
    change (openImmersionCommonMap f g a b h i ≫ pullback.fst f g) w = _
    rw [openImmersionCommonMap_fst]
    exact hw

include hc in
/-- Equality on the prescribed common opens detects equality on the full intersection. -/
theorem openImmersionCommonCover_hom_ext {T : Scheme.{u}}
    (p q : pullback f g ⟶ T)
    (hpq : ∀ i, openImmersionCommonMap f g a b h i ≫ p =
      openImmersionCommonMap f g a b h i ≫ q) : p = q :=
  (openImmersionCommonCover f g a b h hc).hom_ext p q hpq

end FLT.Mazur
