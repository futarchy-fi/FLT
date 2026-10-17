/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleSubgroupGeneratorMarking
public import FLT.Mazur.CyclicOrbitCartierGenerator

/-!
# Compatible comparisons retain prescribed orbit labels

Equality of the marked smooth-group sections identifies their lifts in the
actual subgroup. This also identifies the specified Cartier generators,
including when different labels coincide on the base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
variable {S : Scheme} {E F : GeneralizedEllipticCurve S} {n : ℕ} [NeZero n]
  {H : E.FiniteSubgroup n} {J : F.FiniteSubgroup n} (a : CompatibleIso H J)
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ E.group))
  (ψ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ F.group))
  (hH : H.ideal = E.cyclicMarkingIdeal φ) (hJ : J.ideal = F.cyclicMarkingIdeal ψ)

/-- A prescribed equality of curve labels determines the actual subgroup labels. -/
theorem CompatibleIso.orbitMarking_eq (i j : Multiplicative (ZMod n))
    (hm : φ i ≫ a.curve.hom.group = ψ j) :
    H.orbitMarking φ hH i ≫ a.subgroup.hom = J.orbitMarking ψ hJ j := by
  let _ : Mono J.inclusion := Over.mono_of_mono_left J.inclusion
  apply (cancel_mono J.inclusion).mp
  rw [Category.assoc, ← a.group_inclusion, ← Category.assoc,
    orbitMarking_inclusion, orbitMarking_inclusion]
  exact hm

/-- Preserving label one preserves the actual specified Cartier generator. -/
theorem CompatibleIso.orbitGenerator_eq
    (hm : φ (.ofAdd 1) ≫ a.curve.hom.group = ψ (.ofAdd 1)) :
    H.orbitGenerator φ hH ≫ a.subgroup.hom = J.orbitGenerator ψ hJ :=
  a.orbitMarking_eq φ ψ hH hJ _ _ hm

/-- A prescribed relabeling identifies every generator power in the actual subgroup. -/
theorem CompatibleIso.orbitGenerator_pow_relabel
    (c : MulAut (Multiplicative (ZMod n)))
    (hm : ∀ i, φ i ≫ a.curve.hom.group = ψ (c i)) (m : ℕ) :
    (H.orbitGenerator φ hH ^ m) ≫ a.subgroup.hom =
      J.orbitMarking ψ hJ (c (.ofAdd (m : ZMod n))) := by
  rw [orbitGenerator_pow]
  exact a.orbitMarking_eq φ ψ hH hJ _ _ (hm _)

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
