/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFiniteFiberNeighborhood
public import FLT.Mazur.SchemeUnchangedOpen

/-!
# Proper contractions are unchanged near finite fibers

If the original pullback of functions is invertible on every open, a finite
fiber has an unchanged neighborhood. Properness spreads quasi-finiteness;
affineness then recovers the original restricted morphism from its functions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.ProperFunctionSheafIso
set_option backward.isDefEq.respectTransparency false

variable {X Y : Scheme} (f : X ⟶ Y)
  (hf : ∀ U : Y.Opens, IsIso (f.app U))

include hf

/-- An affine morphism preserving actual functions is an isomorphism. -/
theorem isIso_of_affine [IsAffineHom f] : IsIso f := by
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := .isomorphisms Scheme)
  intro y
  obtain ⟨U, hU, hyU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top y)
  refine ⟨U, hyU, ?_⟩
  let _ : IsAffine U.toScheme := hU
  let _ : IsAffine (f ⁻¹ᵁ U).toScheme := hU.preimage f
  let _ : IsIso (f ∣_ U).appTop := by
    rw [morphismRestrict_appTop]
    let _ := hf (U.ι ''ᵁ ⊤)
    infer_instance
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (arrowIsoSpecΓOfIsAffine (f ∣_ U))).mpr inferInstance

/-- Any affine restriction of the original function-preserving map is unchanged. -/
theorem isIso_restrict_of_affine (U : Y.Opens) [IsAffineHom (f ∣_ U)] :
    IsIso (f ∣_ U) := by
  apply isIso_of_affine
  intro V
  rw [morphismRestrict_app]
  let _ := hf (U.ι ''ᵁ V)
  infer_instance

variable [IsProper f]

/-- Every finite point fiber has a neighborhood where the entire map is unchanged. -/
theorem exists_isIso_neighborhood (y : Y) (hy : (f ⁻¹' {y}).Finite) :
    ∃ U : Y.Opens, y ∈ U ∧ IsIso (f ∣_ U) := by
  let _ : IsProper (f ≫ 𝟙 Y) := by simpa only [Category.comp_id] using inferInstanceAs
    (IsProper f)
  have hq : ∀ x : (f ≫ 𝟙 Y).fiber y,
      f.QuasiFiniteAt ((f ≫ 𝟙 Y).fiberι y x) := by
    intro x
    have hx : f ((f ≫ 𝟙 Y).fiberι y x) = y := ((f ≫ 𝟙 Y).fiberHomeo y x).2
    have hfin : (f ⁻¹' {f ((f ≫ 𝟙 Y).fiberι y x)}).Finite := by rwa [hx]
    have : Finite (f.fiber (f ((f ≫ 𝟙 Y).fiberι y x))) :=
      (f.fiberHomeo _).finite_iff.mpr hfin
    exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _)
  obtain ⟨U, hyU, hU⟩ :=
    Approximation.exists_finite_over_base_neighborhood f (𝟙 Y) y hq
  have he : (𝟙 Y) ⁻¹ᵁ U = U := rfl
  rw [he] at hU
  let _ := hU
  exact ⟨U, hyU, isIso_restrict_of_affine f hf U⟩

/-- A target open with finite original fibers is unchanged scheme-theoretically. -/
theorem isIso_restrict_of_finite_fibers (U : Y.Opens)
    (hU : ∀ y ∈ U, (f ⁻¹' {y}).Finite) : IsIso (f ∣_ U) :=
  SchemeUnchangedOpen.isIso_of_neighborhoods f U
    (fun y hy ↦ exists_isIso_neighborhood f hf y (hU y hy))

end FLT.Mazur.ProperFunctionSheafIso
