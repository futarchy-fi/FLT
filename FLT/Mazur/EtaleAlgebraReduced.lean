/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Smooth.Flat

/-!
# Reducedness of étale algebras over domains

Flatness embeds the algebra into its generic fiber. The generic fiber is
formally unramified over a field and hence reduced, so the original algebra
is reduced as well. No nontriviality assumption on the algebra is needed.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u v

/-- A flat algebra reduced over the total fraction ring is reduced. -/
theorem isReduced_of_flat_generic_fiber (R : Type u) (B : Type v)
    [CommRing R] [CommRing B] [Algebra R B] [Module.Flat R B]
    [IsReduced (FractionRing R ⊗[R] B)] : IsReduced B :=
  isReduced_of_injective (Algebra.TensorProduct.includeRight :
    B →ₐ[R] FractionRing R ⊗[R] B)
    (Algebra.TensorProduct.includeRight_injective
      (IsFractionRing.injective R (FractionRing R)))

/-- Étale algebras over a domain are reduced. -/
theorem isReduced_of_etale_domain (R : Type u) (B : Type v)
    [CommRing R] [IsDomain R] [CommRing B] [Algebra R B] [Algebra.Etale R B] :
    IsReduced B := by
  have : IsReduced (FractionRing R ⊗[R] B) :=
    Algebra.FormallyUnramified.isReduced_of_field (FractionRing R) _
  exact isReduced_of_flat_generic_fiber R B

end FLT.Mazur.Approximation
