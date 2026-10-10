/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineLocalFiberRegularQuotient
public import FLT.Mazur.ResidueFiberRegularLocalization

/-!
# Fiberwise regular equations in a flat Noetherian algebra

An equation in a flat algebra between Noetherian rings is regular with flat
full quotient exactly when it is regular on all residue fibers. In particular,
fiberwise regularity implies regularity after arbitrary algebra base change.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.FiberwiseRegularFlatQuotient
variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]
  [IsNoetherianRing R] [IsNoetherianRing B] [Module.Flat R B]

/-- Residue-fiber regularity constructs total regularity and flatness of the full quotient. -/
theorem regular_and_flat (a : B)
    (ha : ∀ (p : Ideal R) [p.IsPrime], IsRegular (1 ⊗ₜ[R] a : p.ResidueField ⊗[R] B)) :
    IsRegular a ∧ Module.Flat R (B ⧸ Ideal.span {a}) := by
  apply AffineLocalFiberRegularQuotient.regular_and_flat a
  intro q _
  exact ResidueFiberRegularLocalization.regular_localFiber q a (ha (q.under R))

/-- The relative principal Cartier condition is equivalent to regularity on residue fibers. -/
theorem residue_regular_iff (a : B) :
    (∀ (p : Ideal R) [p.IsPrime], IsRegular (1 ⊗ₜ[R] a : p.ResidueField ⊗[R] B)) ↔
      IsRegular a ∧ Module.Flat R (B ⧸ Ideal.span {a}) := by
  constructor
  · exact regular_and_flat a
  · rintro ⟨ha, hq⟩ p _
    let _ := hq
    exact FCurve.isRegular_one_tmul_of_quotient_flat a ha p.ResidueField

/-- Fiberwise regularity gives regularity after every algebra base change. -/
theorem regular_baseChange (a : B)
    (ha : ∀ (p : Ideal R) [p.IsPrime], IsRegular (1 ⊗ₜ[R] a : p.ResidueField ⊗[R] B))
    (S : Type*) [CommRing S] [Algebra R S] :
    IsRegular (1 ⊗ₜ[R] a : S ⊗[R] B) := by
  obtain ⟨hr, hq⟩ := regular_and_flat a ha
  let _ := hq
  exact FCurve.isRegular_one_tmul_of_quotient_flat a hr S

end FLT.Mazur.FiberwiseRegularFlatQuotient
