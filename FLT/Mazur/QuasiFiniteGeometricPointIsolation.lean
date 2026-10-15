/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Isolating one original point without losing its residue embeddings

A quasi-finite morphism admits an affine source neighborhood whose fiber
contains only the specified original point. Every geometric lift on this
neighborhood therefore uses that point, while all its field embeddings
remain available. The coefficient scheme is unchanged.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.QuasiFiniteGeometricPointIsolation
set_option backward.isDefEq.respectTransparency false
variable {E S : Scheme} (e : E ⟶ S) [LocallyQuasiFinite e] [LocallyOfFiniteType e]

/-- A constructed original affine neighborhood isolates the selected point of its fiber. -/
theorem exists_affine_open (x : E) :
    ∃ U : E.Opens, IsAffineOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, e y = e x → y = x := by
  have ho := Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp (e.quasiFiniteAt x)
  have ho' : IsOpen ({⟨x, rfl⟩} : Set (e ⁻¹' {e x})) := by
    simpa only [Set.image_singleton, Scheme.Hom.asFiber, Homeomorph.apply_symm_apply]
      using (e.fiberHomeo (e x)).isOpenMap _ ho
  obtain ⟨V, hV, hpre⟩ := isOpen_induced_iff.mp ho'
  have hxV : x ∈ V := by
    have hx : (⟨x, rfl⟩ : e ⁻¹' {e x}) ∈ ({⟨x, rfl⟩} : Set (e ⁻¹' {e x})) := rfl
    rw [← hpre] at hx
    exact hx
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset (U := ⟨V, hV⟩) hxV
  refine ⟨U, hU, hxU, fun y hy hey ↦ ?_⟩
  have h : (⟨y, hey⟩ : e ⁻¹' {e x}) ∈ ({⟨x, rfl⟩} : Set (e ⁻¹' {e x})) := by
    rw [← hpre]
    exact hUV hy
  exact congrArg Subtype.val (Set.mem_singleton_iff.mp h)

/-- Every whole geometric lift in the refined fiber retains the same original image point. -/
theorem exists_affine_geometric_factor {K : Type} [Field K] (z : Spec (.of K) ⟶ E) :
    ∃ (A : Scheme) (q : A ⟶ E) (w : Spec (.of K) ⟶ A),
      IsAffine A ∧ IsOpenImmersion q ∧ w ≫ q = z ∧
      ∀ v : Spec (.of K) ⟶ A, v ≫ q ≫ e = z ≫ e →
        (v ≫ q) default = z default := by
  obtain ⟨U, hU, hz, hsingle⟩ := exists_affine_open e (z default)
  have hr : Set.range z ⊆ Set.range U.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    rw [Subsingleton.elim x default]
    exact hz
  let w := IsOpenImmersion.lift U.ι z hr
  refine ⟨U.toScheme, U.ι, w, hU, inferInstance,
    IsOpenImmersion.lift_fac _ _ _, fun v hv ↦ ?_⟩
  apply hsingle _ (v default).property
  exact congrArg (fun g : Spec (.of K) ⟶ S ↦ g default) hv

end FLT.Mazur.QuasiFiniteGeometricPointIsolation
