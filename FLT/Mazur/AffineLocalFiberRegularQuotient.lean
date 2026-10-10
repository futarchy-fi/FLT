/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrimeLocalFiberRegularQuotient
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Descending the local fiber criterion to an affine equation

Regularity in every ambient local closed fiber implies regularity in the
original ring and flatness of its full principal quotient. The quotient
localizations are the actual tensor products, identified with quotient rings
by the canonical ideal-extension equivalence.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.AffineLocalFiberRegularQuotient
variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]
  [IsNoetherianRing R] [IsNoetherianRing B] [Module.Flat R B]

/-- The equation is regular on every closed fiber of an ambient local ring. -/
def LocalFiberRegular (a : B) : Prop :=
  ∀ (q : Ideal B) [q.IsMaximal],
    let _ := Localization.AtPrime.algebraOfLiesOver (q.under R) q
    IsRegular (1 ⊗ₜ[Localization.AtPrime (q.under R)]
      algebraMap B (Localization.AtPrime q) a :
        IsLocalRing.ResidueField (Localization.AtPrime (q.under R))
          ⊗[Localization.AtPrime (q.under R)] Localization.AtPrime q)

/-- Local closed-fiber regularity detects regularity of the original equation. -/
theorem regular (a : B) (ha : LocalFiberRegular (R := R) a) : IsRegular a := by
  rw [← isLeftRegular_iff_isRegular]
  intro x y hxy
  apply Module.eq_of_localization_maximal
    (fun q _ ↦ Localization.AtPrime q) (fun q _ ↦ Algebra.linearMap B _) x y
  intro q _
  apply (PrimeLocalFiberRegularQuotient.regular_and_flat q a (ha q)).1.left
  change algebraMap B (Localization.AtPrime q) a * algebraMap B _ x =
    algebraMap B (Localization.AtPrime q) a * algebraMap B _ y
  simpa only [← map_mul] using congrArg (algebraMap B (Localization.AtPrime q)) hxy

/-- Local closed-fiber regularity constructs flatness of the full original quotient. -/
theorem quotient_flat (a : B) (ha : LocalFiberRegular (R := R) a) :
    Module.Flat R (B ⧸ Ideal.span {a}) := by
  let I : Ideal B := Ideal.span {a}
  apply Module.flat_of_isLocalized_maximal B (B ⧸ I)
    (fun q _ ↦ Localization.AtPrime q ⊗[B] (B ⧸ I))
    (fun q _ ↦ TensorProduct.mk B (Localization.AtPrime q) (B ⧸ I) 1)
  intro q _
  have hq := (PrimeLocalFiberRegularQuotient.regular_and_flat q a (ha q)).2
  have hI : I.map (algebraMap B (Localization.AtPrime q)) =
      Ideal.span {algebraMap B (Localization.AtPrime q) a} := by
    simp only [I, Ideal.map_span, Set.image_singleton]
  let _ : Module.Flat R
      (Localization.AtPrime q ⧸ I.map (algebraMap B (Localization.AtPrime q))) := by
    let _ := hq
    exact Module.Flat.of_linearEquiv (Ideal.quotientEquivAlgOfEq R hI).toLinearEquiv
  let e := Algebra.TensorProduct.quotIdealMapEquivTensorQuot (Localization.AtPrime q) I
  exact Module.Flat.of_linearEquiv (e.symm.toLinearEquiv.restrictScalars R)

/-- The affine equation defines a regular principal ideal with flat full quotient. -/
theorem regular_and_flat (a : B) (ha : LocalFiberRegular (R := R) a) :
    IsRegular a ∧ Module.Flat R (B ⧸ Ideal.span {a}) :=
  ⟨regular a ha, quotient_flat a ha⟩

end FLT.Mazur.AffineLocalFiberRegularQuotient
