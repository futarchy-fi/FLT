/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Deformations.RepresentationTheory.FlatCofinal
public import FLT.Deformations.RepresentationTheory.PadicIdealCofinal
public import FLT.Deformations.RepresentationTheory.PadicIdealOpen

/-!
# Flatness over finite free p-adic coefficient rings

To check every open coefficient quotient, it suffices to construct finite-flat
models modulo every power of p. Openness and cofinality follow from the module
topology; the existence of the torsion models remains an arithmetic obligation.
-/

@[expose] public section

open NumberField

universe u

namespace GaloisRep

variable {K M : Type u} {A : Type} [Field K] [NumberField K]
  [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLocalRing A]
  [AddCommGroup M] [Module A M] [Module.Free A M] [Module.Finite A M]
  (p : ℕ) [Fact p.Prime] [Algebra ℤ_[p] A]
  [Module.Finite ℤ_[p] A] [Module.Free ℤ_[p] A] [IsModuleTopology ℤ_[p] A]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (ρ : GaloisRep K A M)

/-- Over a finite free p-adic coefficient ring, flatness is equivalent to
finite-flat prolongations of all p-power reductions. -/
theorem isFlatAt_iff_powers :
    ρ.IsFlatAt v ↔ ∀ n : ℕ,
      (ρ.baseChange (A ⧸ Ideal.span {(p : A) ^ n})).HasFlatProlongationAt v := by
  let := IsModuleTopology.isTopologicalModule (R := ℤ_[p]) (M := A)
  exact isFlatAt_iff_of_cofinal_powers v ρ p
    (PadicInt.isOpen_span_p_pow p A) (PadicInt.exists_p_pow_le_of_isOpen p A)

end GaloisRep
