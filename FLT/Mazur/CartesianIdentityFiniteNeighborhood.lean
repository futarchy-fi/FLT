/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartesianIdentityQuasiFinite
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# A finite neighborhood of an entire Cartesian identity

For a proper map, remove the closed image of the non-quasi-finite locus.
A Cartesian identity lies in the resulting target open, and the original
map is finite over this one open containing the whole identity image.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CartesianIdentity
universe u
variable {T X Y : Scheme.{u}} (i : T ⟶ X) (f : X ⟶ Y)
  (h : IsPullback (𝟙 T) i (i ≫ f) f) [IsProper f]

/-- The complement of the proper image of the actual non-quasi-finite locus. -/
def finiteTargetOpen : Y.Opens :=
  ⟨(f '' (f.quasiFiniteLocus : Set X)ᶜ)ᶜ,
    (f.isClosedMap _ f.quasiFiniteLocus.isOpen.isClosed_compl).isOpen_compl⟩

include h in
/-- The entire test image avoids the closed bad locus. -/
theorem image_mem_finiteTargetOpen (t : T) : f (i t) ∈ finiteTargetOpen f := by
  rintro ⟨x, hx, he⟩
  have hxt : x = i t := by
    have hm : x ∈ f ⁻¹' {f (i t)} := he
    rwa [preimage_singleton i f h t, Set.mem_singleton_iff] at hm
  exact hx (hxt ▸ quasiFiniteAt i f h t)

/-- Over the retained target open the original proper map is finite. -/
theorem finite_restrict_finiteTargetOpen : IsFinite (f ∣_ finiteTargetOpen f) := by
  have : LocallyQuasiFinite (f ∣_ finiteTargetOpen f) := by
    rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
    apply top_unique
    intro x _
    have hx : f.QuasiFiniteAt ((f ⁻¹ᵁ finiteTargetOpen f).ι x) := by
      by_contra hn
      exact x.property ⟨_, hn, rfl⟩
    rw [← Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion,
      ← morphismRestrict_ι, Scheme.Hom.quasiFiniteAt_comp_iff] at hx
    exact hx
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

include h in
/-- Every Cartesian identity has one finite target neighborhood containing its full image. -/
theorem exists_finite_identity_neighborhood :
    ∃ U : Y.Opens, Set.range (i ≫ f) ⊆ U ∧ IsFinite (f ∣_ U) := by
  refine ⟨finiteTargetOpen f, ?_, finite_restrict_finiteTargetOpen f⟩
  rintro _ ⟨t, rfl⟩
  exact image_mem_finiteTargetOpen i f h t

end FLT.Mazur.CartesianIdentity
