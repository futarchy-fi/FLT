/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicResidualIntegerCongruence
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph

/-!
# The spectra of the actual residual congruence subrings

Inside the finite fixed ring, impose the original full arrow equations modulo
a positive integer. The resulting inclusion is a spectral homeomorphism because
every finite fixed function has a positive power satisfying those equations.
These are congruence subrings, not asserted to be reductions of the full invariant ring.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (i : InvariantAffineIndex n) (m : ℕ)

/-- Finite fixed functions satisfying the actual full residual equations modulo an integer. -/
def affineRelabelCongruence : Subring (affineRelabelSections n i) :=
  let q := Ideal.Quotient.mk
    (Ideal.span {(m : Γ((affineResidualDomain n i).toScheme, ⊤))})
  RingHom.eqLocus
    ((q.comp (affineResidualSource n i).appTop.hom).comp (affineRelabelSections n i).subtype)
    ((q.comp (affineResidualTarget n i).appTop.hom).comp (affineRelabelSections n i).subtype)

/-- The congruence condition is precisely membership of the original discrepancy in `(m)`. -/
theorem mem_affineRelabelCongruence (s : affineRelabelSections n i) :
    s ∈ affineRelabelCongruence n i m ↔
      (affineResidualSource n i).appTop s.val - (affineResidualTarget n i).appTop s.val ∈
        Ideal.span {(m : Γ((affineResidualDomain n i).toScheme, ⊤))} :=
  Ideal.Quotient.eq

/-- Full residual functions map into every actual integer-congruence subring. -/
def affineResidualToCongruence :
    affineResidualSections n i →+* affineRelabelCongruence n i m :=
  (affineResidualToRelabel n i).codRestrict _ (fun s => by
    apply (mem_affineRelabelCongruence n i m _).mpr
    change (affineResidualSource n i).appTop s.val -
      (affineResidualTarget n i).appTop s.val ∈ _
    rw [s.property, sub_self]
    exact Ideal.zero_mem _)

/-- One positive power sends the whole finite fixed ring into the full congruence subring. -/
theorem affineRelabelCongruence_uniform_power (hm : 0 < m) :
    ∃ e : ℕ, 0 < e ∧ ∀ s : affineRelabelSections n i,
      s ^ e ∈ affineRelabelCongruence n i m := by
  obtain ⟨e, he, h⟩ := affineRelabel_uniform_power_congruence n i m hm
  exact ⟨e, he, fun s => (mem_affineRelabelCongruence n i m (s ^ e)).mpr (h s)⟩

/-- Every positive-modulus congruence subring has the same spectrum as the finite fixed ring. -/
theorem affineRelabelCongruence_spectrum_isHomeomorph (hm : 0 < m) :
    IsHomeomorph (PrimeSpectrum.comap (affineRelabelCongruence n i m).subtype) := by
  obtain ⟨e, he, h⟩ := affineRelabelCongruence_uniform_power n i m hm
  apply PrimeSpectrum.isHomeomorph_comap _ (fun s => ⟨e, he, ⟨⟨s ^ e, h s⟩, rfl⟩⟩)
  rw [(RingHom.injective_iff_ker_eq_bot _).mp Subtype.val_injective]
  exact bot_le

end FLT.Mazur.CyclicCharacteristicOrbit
