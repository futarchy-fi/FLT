/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.RingTheory.Nakayama

/-!
# Full local rigidity from scalar generation to first order

In a local source with finitely generated maximal ideal, generation by scalar
images modulo the square of the maximal ideal upgrades to exact generation
by Nakayama. Together with separable residue fields this proves full local
unramifiedness. The source may be nonreduced and the scalar ring need not be
Noetherian.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarFirstOrderLocalRigidity
open IsLocalRing
variable {A : Type} [CommRing A] [IsLocalRing A]

/-- First-order generation of the maximal ideal upgrades to exact generation. -/
theorem ideal_eq_maximal (J : Ideal A) (hJ : J ≤ maximalIdeal A)
    (hfg : (maximalIdeal A).FG)
    (h : maximalIdeal A ≤ J ⊔ maximalIdeal A ^ 2) : J = maximalIdeal A := by
  apply le_antisymm hJ
  apply Submodule.le_of_le_smul_of_le_jacobson_bot hfg
    (I := maximalIdeal A)
  · exact (jacobson_eq_maximalIdeal (⊥ : Ideal A) bot_ne_top).ge
  · simpa only [Ideal.smul_eq_mul, pow_two] using h

variable {R : Type} [CommRing R] [IsLocalRing R] [Algebra R A]
  [IsLocalHom (algebraMap R A)] [Algebra.EssFiniteType R A]
  [Algebra.IsSeparable (ResidueField R) (ResidueField A)]

/-- Separable residues and scalar generation modulo the maximal-ideal square kill full tangents. -/
theorem formallyUnramified (hfg : (maximalIdeal A).FG)
    (h : maximalIdeal A ≤ (maximalIdeal R).map (algebraMap R A) ⊔ maximalIdeal A ^ 2) :
    Algebra.FormallyUnramified R A := by
  apply Algebra.FormallyUnramified.of_map_maximalIdeal
  apply ideal_eq_maximal _ ?_ hfg h
  exact ((local_hom_TFAE (algebraMap R A)).out 1 3 rfl rfl).mp inferInstance

/-- Source Noetherianity supplies the only ideal finiteness used in the first-order test. -/
theorem formallyUnramified_of_noetherian [IsNoetherianRing A]
    (h : maximalIdeal A ≤ (maximalIdeal R).map (algebraMap R A) ⊔ maximalIdeal A ^ 2) :
    Algebra.FormallyUnramified R A :=
  formallyUnramified (IsNoetherian.noetherian _) h

end FLT.Mazur.ScalarFirstOrderLocalRigidity
