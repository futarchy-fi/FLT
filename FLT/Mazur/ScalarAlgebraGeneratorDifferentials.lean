/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarFiniteDifferentialGenerators
public import Mathlib.RingTheory.Etale.Kaehler

/-!
# Constructing differential generators from algebra generators

An actual algebra generating family spans the full relative differentials.
These generators still span after any source localization, so equations for
presentation coordinates suffice for the stalk Jacobian tests. A finite
family also constructs differential finiteness without scalar Noetherianity.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarAlgebraGeneratorDifferentials
variable {R A L ι : Type} [CommRing R] [CommRing A] [CommRing L] [Algebra R A]

/-- Algebra generators span all differentials, including the nonreduced directions. -/
theorem span_eq_top (z : ι → A) (hz : Algebra.adjoin R (Set.range z) = ⊤) :
    Submodule.span A (Set.range fun i ↦ KaehlerDifferential.D R A (z i)) = ⊤ := by
  let N := Submodule.span A (Set.range fun i ↦ KaehlerDifferential.D R A (z i))
  have hd : N.mkQ.compDer (KaehlerDifferential.D R A) = 0 := by
    apply Derivation.ext_of_adjoin_eq_top (Set.range z) hz
    rintro _ ⟨i, rfl⟩
    exact (Submodule.Quotient.mk_eq_zero N).mpr (Submodule.subset_span ⟨i, rfl⟩)
  apply top_unique
  rw [← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  exact (Submodule.Quotient.mk_eq_zero N).mp (DFunLike.congr_fun hd a)

/-- A finite algebra presentation constructs finite relative differentials. -/
theorem finite [Finite ι] (z : ι → A) (hz : Algebra.adjoin R (Set.range z) = ⊤) :
    Module.Finite A (KaehlerDifferential R A) := by
  constructor
  rw [← span_eq_top z hz]
  exact Submodule.fg_span (Set.finite_range _)

variable [Algebra A L] [Algebra R L] [IsScalarTower R A L]

/-- The original algebra generators span differentials in any full source localization. -/
theorem span_localization (N : Submonoid A) [IsLocalization N L]
    (z : ι → A) (hz : Algebra.adjoin R (Set.range z) = ⊤) :
    Submodule.span L (Set.range fun i ↦
      KaehlerDifferential.D R L (algebraMap A L (z i))) = ⊤ := by
  have h := span_eq_top_of_isLocalizedModule L N (KaehlerDifferential.map R R A L)
    (v := Set.range fun i ↦ KaehlerDifferential.D R A (z i)) (span_eq_top z hz)
  simpa only [← Set.range_comp, Function.comp_def, KaehlerDifferential.map_D] using h

end FLT.Mazur.ScalarAlgebraGeneratorDifferentials
