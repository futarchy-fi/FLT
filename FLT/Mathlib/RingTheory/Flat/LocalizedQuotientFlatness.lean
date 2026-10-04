/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Submodule

/-! # Relative flatness of a quotient can be checked in ambient localizations -/

@[expose] public noncomputable section

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Check flatness of `S/J` over the original base in every maximal
localization of the ambient algebra `S`. -/
theorem flat_quotient_of_localized (J : Ideal S)
    (h : ∀ (P : Ideal S) [P.IsMaximal],
      Module.Flat R (Localization.AtPrime P ⧸ J.map (algebraMap S (Localization.AtPrime P)))) :
    Module.Flat R (S ⧸ J) := by
  let Jp (P : Ideal S) [P.IsMaximal] :=
    J.localized' (Localization.AtPrime P) P.primeCompl
      (Algebra.linearMap S (Localization.AtPrime P))
  apply Module.flat_of_isLocalized_maximal S (S ⧸ J)
    (fun P ↦ Localization.AtPrime P ⧸ Jp P)
    (fun P ↦ J.toLocalizedQuotient' (Localization.AtPrime P) P.primeCompl
      (Algebra.linearMap S (Localization.AtPrime P)))
  intro P _
  have he : Jp P = J.map (algebraMap S (Localization.AtPrime P)) := by
    dsimp only [Jp]
    rw [Submodule.localized'_eq_span]
    rfl
  change Module.Flat R (Localization.AtPrime P ⧸ Jp P)
  rw [he]
  exact h P

end Ideal
