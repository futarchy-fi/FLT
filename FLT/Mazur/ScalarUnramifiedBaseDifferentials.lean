/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarAlgebraGeneratorDifferentials

/-!
# Differential generation over an unramified scalar extension

Generators over localized scalars also generate differentials over the
original scalar ring. The scalar extension contributes no differentials;
the proof retains the full algebra and does not require it to be reduced.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarUnramifiedBaseDifferentials
variable {R T L ι : Type} [CommRing R] [CommRing T] [CommRing L]
  [Algebra R T] [Algebra T L] [Algebra R L] [IsScalarTower R T L]
  [Algebra.FormallyUnramified R T]

/-- Scalars in an unramified extension have zero original-base differential in every algebra. -/
theorem scalar_derivative_eq_zero (t : T) :
    KaehlerDifferential.D R L (algebraMap T L t) = 0 := by
  rw [← KaehlerDifferential.map_D R R T L]
  rw [Subsingleton.elim (KaehlerDifferential.D R T t) 0, map_zero]

/-- Algebra generators over an unramified extension span all original-base differentials. -/
theorem span_eq_top (z : ι → L) (hz : Algebra.adjoin T (Set.range z) = ⊤) :
    Submodule.span L (Set.range fun i ↦ KaehlerDifferential.D R L (z i)) = ⊤ := by
  let N := Submodule.span L (Set.range fun i ↦ KaehlerDifferential.D R L (z i))
  have hd (a : L) : KaehlerDifferential.D R L a ∈ N := by
    have ha : a ∈ Algebra.adjoin T (Set.range z) := hz.symm ▸ trivial
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Submodule.subset_span ⟨i, rfl⟩
    | algebraMap t =>
      rw [scalar_derivative_eq_zero (R := R)]
      exact N.zero_mem
    | add x y _ _ hx hy =>
      rw [map_add]
      exact N.add_mem hx hy
    | mul x y _ _ hx hy =>
      rw [Derivation.leibniz]
      exact N.add_mem (N.smul_mem x hy) (N.smul_mem y hx)
  apply top_unique
  rw [← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  exact hd a

end FLT.Mazur.ScalarUnramifiedBaseDifferentials
