/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeComparisonClosedObstruction
public import FLT.Mazur.SchemeScalarImageQuotient
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import Mathlib.AlgebraicGeometry.Morphisms.Integral

/-!
# Geometry of the original scalar kernel pair over its exact image

The original scalar kernel pair is also the kernel pair over the exact image.
Etale image geometry makes a monic relation comparison open. Integral image
geometry makes its missed image closed, so fiber coverage extends to an open.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeScalarImageKernelGeometry
open SchemeScalarImageQuotient SchemeComparisonCoverageLocus
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {D X : Scheme.{0}}
  (f : X ⟶ Spec (.of R))
local notation "c" => projection f
local notation "u" => pullback.fst f f
local notation "v" => pullback.snd f f

/-- The original scalar kernel pair retains exactly the full image equations. -/
theorem kernel_isPullback : IsPullback u v c c := by
  apply IsPullback.of_isLimit («c» := PullbackCone.mk u v
    ((projection_eq_iff f u v).mpr pullback.condition))
  apply PullbackCone.isLimitAux'
  intro s
  have hs := (projection_eq_iff f s.fst s.snd).mp s.condition
  refine ⟨pullback.lift s.fst s.snd hs, pullback.lift_fst _ _ _,
    pullback.lift_snd _ _ _, ?_⟩
  intro m hm₁ hm₂
  exact (IsPullback.of_hasPullback f f).hom_ext
    (hm₁.trans (pullback.lift_fst _ _ _).symm)
    (hm₂.trans (pullback.lift_snd _ _ _).symm)

/-- The original kernel first projection is etale over an etale exact image. -/
theorem kernelFirst_etale [Etale c] : Etale u :=
  MorphismProperty.of_isPullback (kernel_isPullback f).flip inferInstance

/-- Integral exact image geometry makes the full original kernel image map integral. -/
theorem kernelImage_integral [IsIntegralHom c] : IsIntegralHom (u ≫ c) := by
  let _ : IsIntegralHom u :=
    MorphismProperty.of_isPullback (kernel_isPullback f).flip inferInstance
  infer_instance

variable (a b : D ⟶ X) (h : a ≫ f = b ≫ f)
local notation "k" => pullback.lift a b h

/-- An etale endpoint and etale exact image make the original full comparison etale. -/
theorem comparison_etale [Etale a] [Etale c] : Etale k := by
  let _ := kernelFirst_etale f
  let _ : Etale (k ≫ u) := by rw [pullback.lift_fst]; infer_instance
  exact Etale.of_comp k u

/-- Monicity upgrades the etale original comparison to an open immersion. -/
theorem comparison_isOpenImmersion [Etale a] [Etale c] [Mono k] : IsOpenImmersion k := by
  let _ := comparison_etale f a b h
  exact IsOpenImmersion.of_flat_of_mono k

/-- Etale integral image geometry closes the whole original comparison obstruction. -/
theorem comparison_missedImage_isClosed [Etale a] [Etale c] [IsIntegralHom c] [Mono k] :
    IsClosed ((u ≫ c) '' (Set.range k)ᶜ) := by
  let _ := comparison_isOpenImmersion f a b h
  let _ := kernelImage_integral f
  exact missedImage_isClosed k (u ≫ c)

/-- Coverage of a full original image fiber extends to a surjective comparison neighborhood. -/
theorem exists_comparison_neighborhood [Etale a] [Etale c] [IsIntegralHom c] [Mono k]
    (z : Spec (.of (Scalars f)))
    (hz : ∀ w : (pullback f f : Scheme), (u ≫ c) w = z → w ∈ Set.range k) :
    ∃ U : (Spec (.of (Scalars f))).Opens, z ∈ U ∧ Surjective (k ∣_ ((u ≫ c) ⁻¹ᵁ U)) :=
  exists_neighborhood_of_fiber_coverage k (u ≫ c)
    (comparison_missedImage_isClosed f a b h) z hz

end FLT.Mazur.SchemeScalarImageKernelGeometry
