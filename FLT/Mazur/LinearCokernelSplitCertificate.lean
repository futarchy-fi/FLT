/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# A finite-equation certificate for a split cokernel

An inner inverse of a presentation map splits its whole cokernel. Conversely,
projectivity constructs an inner inverse without choosing generators of every
individual relation. This is the linear algebra behind uniform descent for
finite module presentations.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.LinearCokernel
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- An inner inverse splits the entire cokernel of a map into a projective module. -/
theorem projective_of_innerInverse [Module.Projective R N]
    (f : M →ₗ[R] N) (g : N →ₗ[R] M) (h : (f.comp g).comp f = f) :
    Module.Projective R (N ⧸ LinearMap.range f) := by
  let p := LinearMap.range f
  let e : N →ₗ[R] N := LinearMap.id - f.comp g
  have he : p ≤ LinearMap.ker e := by
    rintro _ ⟨x, rfl⟩
    change f x - f (g (f x)) = 0
    exact sub_eq_zero.mpr (LinearMap.congr_fun h x).symm
  apply Module.Projective.of_split (p.liftQ e he) p.mkQ
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := p.mkQ_surjective x
  change p.mkQ (e y) = p.mkQ y
  change p.mkQ (y - f (g y)) = p.mkQ y
  rw [map_sub, show p.mkQ (f (g y)) = 0 from
    (Submodule.Quotient.mk_eq_zero p).mpr ⟨g y, rfl⟩, sub_zero]

/-- Projectivity of a cokernel supplies an inner inverse of its presentation map. -/
theorem exists_innerInverse_of_projective [Module.Projective R N]
    (f : M →ₗ[R] N) [Module.Projective R (N ⧸ LinearMap.range f)] :
    ∃ g : N →ₗ[R] M, (f.comp g).comp f = f := by
  let p := LinearMap.range f
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p.mkQ LinearMap.id p.mkQ_surjective
  let e : N →ₗ[R] N := LinearMap.id - s.comp p.mkQ
  have he (x : N) : e x ∈ p := by
    apply (Submodule.Quotient.mk_eq_zero p).mp
    change p.mkQ (x - s (p.mkQ x)) = 0
    rw [map_sub, show p.mkQ (s (p.mkQ x)) = p.mkQ x from
      LinearMap.congr_fun hs (p.mkQ x), sub_self]
  obtain ⟨g, hg⟩ := Module.projective_lifting_property f.rangeRestrict
    (e.codRestrict p he) f.surjective_rangeRestrict
  refine ⟨g, ?_⟩
  ext x
  have hx := congrArg Subtype.val (LinearMap.congr_fun hg (f x))
  change f (g (f x)) = f x
  change f (g (f x)) = f x - s (p.mkQ (f x)) at hx
  rw [show p.mkQ (f x) = 0 from
    (Submodule.Quotient.mk_eq_zero p).mpr ⟨x, rfl⟩, map_zero, sub_zero] at hx
  exact hx

/-- The split-cokernel condition is one equation between linear maps. -/
theorem projective_iff_innerInverse [Module.Projective R N] (f : M →ₗ[R] N) :
    Module.Projective R (N ⧸ LinearMap.range f) ↔
      ∃ g : N →ₗ[R] M, (f.comp g).comp f = f := by
  constructor
  · intro h
    let _ := h
    exact exists_innerInverse_of_projective f
  · rintro ⟨g, hg⟩
    exact projective_of_innerInverse f g hg

end FLT.Mazur.LinearCokernel
