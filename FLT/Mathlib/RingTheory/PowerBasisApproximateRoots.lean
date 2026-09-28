/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.PowerBasis
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Approximate roots and maps out of a monogenic algebra

For an algebra with a power basis, maps into `B / I` are equivalent to roots
of the generator's minimal polynomial modulo `I`. Exact lifting of a given
map requires a root with the prescribed reduction; existence of some map
into `B` merely requires some root in `B`.
-/

@[expose] public noncomputable section

namespace PowerBasis

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (pb : PowerBasis R A) (I : Ideal B)

/-- An algebra map to a quotient exists precisely when the defining minimal
polynomial has an approximate root in the original ring. -/
theorem nonempty_algHom_quotient_iff :
    Nonempty (A →ₐ[R] B ⧸ I) ↔
      ∃ y : B, Polynomial.aeval y (minpoly R pb.gen) ∈ I := by
  constructor
  · rintro ⟨f⟩
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (f pb.gen)
    refine ⟨y, ?_⟩
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    change (Ideal.Quotient.mkₐ R I) (Polynomial.aeval y (minpoly R pb.gen)) = 0
    rw [← Polynomial.aeval_algHom_apply]
    change Polynomial.aeval (Ideal.Quotient.mk I y) (minpoly R pb.gen) = 0
    rw [hy, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  · rintro ⟨y, hy⟩
    refine ⟨pb.lift ((Ideal.Quotient.mkₐ R I) y) ?_⟩
    rw [Polynomial.aeval_algHom_apply]
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr hy

/-- Exact lifting of a specified quotient map requires a genuine root with
the specified reduction of the generator. -/
theorem exists_algHom_lift_iff (f : A →ₐ[R] B ⧸ I) :
    (∃ g : A →ₐ[R] B, (Ideal.Quotient.mkₐ R I).comp g = f) ↔
      ∃ y : B, Polynomial.aeval y (minpoly R pb.gen) = 0 ∧
        Ideal.Quotient.mk I y = f pb.gen := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g pb.gen, ?_, DFunLike.congr_fun hg pb.gen⟩
    rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  · rintro ⟨y, hy, hf⟩
    refine ⟨pb.lift y hy, pb.algHom_ext ?_⟩
    simpa only [AlgHom.comp_apply, lift_gen, Ideal.Quotient.mkₐ_eq_mk] using hf

/-- Existence of an integral map needs a root, with no prescribed congruence. -/
theorem nonempty_algHom_iff :
    Nonempty (A →ₐ[R] B) ↔ ∃ y : B, Polynomial.aeval y (minpoly R pb.gen) = 0 := by
  constructor
  · rintro ⟨f⟩
    exact ⟨f pb.gen, (pb.liftEquiv f).property⟩
  · rintro ⟨y, hy⟩
    exact ⟨pb.lift y hy⟩

end PowerBasis
