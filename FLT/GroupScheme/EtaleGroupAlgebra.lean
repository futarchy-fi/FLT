/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.DiagonalizableFiniteFlat
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Smooth.Fiber

/-!
# Étale finite group algebras when the group order is invertible

Differentiating the order relation for each group element kills every basis
differential. The finite free group algebra is therefore étale.
-/

@[expose] public noncomputable section

namespace MonoidAlgebra

/-- A finite commutative group algebra is étale whenever the group order is
invertible in the coefficient ring. -/
theorem etale_of_isUnit_card (R G : Type) [CommRing R] [CommGroup G] [Finite G]
    (hn : IsUnit (Nat.card G : R)) : Algebra.Etale R (MonoidAlgebra R G) := by
  let A := MonoidAlgebra R G
  let D := KaehlerDifferential.D R A
  have hD : D.toLinearMap = 0 := by
    apply (MonoidAlgebra.basis G R).ext
    intro g
    change D (single g 1) = 0
    have hp : (single g (1 : R)) ^ Nat.card G = 1 := by
      rw [single_pow, pow_card_eq_one', one_pow]
      rfl
    have hu : IsUnit (single g (1 : R)) :=
      IsUnit.of_pow_eq_one hp (Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩)
    have h := D.leibniz_pow (single g 1) (Nat.card G)
    rw [hp, D.map_one_eq_zero] at h
    have hnA : IsUnit (Nat.card G : A) := by
      simpa only [map_natCast] using hn.map (algebraMap R A)
    apply (hu.pow (Nat.card G - 1)).smul_eq_zero.mp
    apply hnA.smul_eq_zero.mp
    simpa only [Nat.cast_smul_eq_nsmul] using h.symm
  let : Algebra.FormallyUnramified R A := by
    constructor
    suffices (⊤ : Submodule A (KaehlerDifferential R A)) ≤ ⊥ from
      (subsingleton_iff_forall_eq 0).mpr fun y ↦ this trivial
    rw [← KaehlerDifferential.span_range_derivation, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact LinearMap.congr_fun hD x
  let : Module.FinitePresentation R A := Module.finitePresentation_of_projective R A
  let : Algebra.FinitePresentation R A := Algebra.FinitePresentation.of_finitePresentation R A
  exact Algebra.Etale.of_formallyUnramified_of_flat

end MonoidAlgebra
