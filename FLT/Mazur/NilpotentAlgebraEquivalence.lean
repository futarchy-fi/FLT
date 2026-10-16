/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NilpotentAlgebraAutomorphism

/-!
# Nilpotent perturbations of algebra equivalences

An algebra map congruent to an independently constructed equivalence modulo a
nilpotent base ideal is invertible, without finiteness or flatness assumptions.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.NilpotentAlgebraEquivalence
variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (I : Ideal R) (hI : IsNilpotent I)
  (e : A ≃ₐ[R] B) (f : A →ₐ[R] B)
  (hf : ∀ x, f x - e x ∈ I.map (algebraMap R B))

include hI hf in
/-- Finite nilpotent correction inverts a perturbation of an arbitrary algebra equivalence. -/
theorem bijective : Function.Bijective f := by
  have hi : ∀ x, (f.comp e.symm.toAlgHom) x - x ∈ I.map (algebraMap R B) := by
    intro x
    simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
      using hf (e.symm x)
  have hb := NilpotentAlgebraAutomorphism.bijective I (f.comp e.symm.toAlgHom) hi hI
  constructor
  · intro x y hxy
    apply e.injective
    apply hb.1
    simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] using hxy
  · intro y
    obtain ⟨x, hx⟩ := hb.2 y
    exact ⟨e.symm x, hx⟩

/-- The inverse is constructed from the given map and the nilpotent comparison. -/
def equiv : A ≃ₐ[R] B := AlgEquiv.ofBijective f (bijective I hI e f hf)

/-- The constructed equivalence preserves the entire original map. -/
theorem equiv_toAlgHom : (equiv I hI e f hf).toAlgHom = f := rfl

/-- Any commuting square between invertible forward maps also commutes on their inverses. -/
theorem inverse_square {C D : Type*} [CommRing C] [CommRing D]
    [Algebra R C] [Algebra R D] (e' : C ≃ₐ[R] D)
    (g : A →ₐ[R] C) (h : B →ₐ[R] D)
    (he : h.comp e.toAlgHom = e'.toAlgHom.comp g) :
    g.comp e.symm.toAlgHom = e'.symm.toAlgHom.comp h := by
  ext x
  apply e'.injective
  have hx := congrArg (fun k : A →ₐ[R] D ↦ k (e.symm x)) he
  simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply] using hx.symm

end FLT.Mazur.NilpotentAlgebraEquivalence
