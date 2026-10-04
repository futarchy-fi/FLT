/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.WittCoefficientRing
public import FLT.Deformations.Categories

/-!
# Residual scalar compatibility for Witt coefficients

The constructed residue identification respects any given p-adic algebra
structure on the finite field. The same complete coefficient ring is an object
of the existing deformation category with its maximal-ideal topology.
-/

@[expose] public noncomputable section
namespace Deformation.WittCoefficients
variable (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [CharP k p]

/-- A p-adic scalar map to a characteristic-p field is forced by reduction modulo p. -/
theorem padicHom_apply (f : ℤ_[p] →+* k) (x : ℤ_[p]) :
    f x = ((PadicInt.toZMod x).val : k) := by
  have hle : IsLocalRing.maximalIdeal ℤ_[p] ≤ RingHom.ker f := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_le]
    intro a ha
    rcases Set.mem_singleton_iff.mp ha with rfl
    change f (p : ℤ_[p]) = 0
    rw [map_natCast, CharP.cast_eq_zero]
  have h := hle (PadicInt.toZMod_spec x)
  rw [ZMod.cast_eq_val] at h
  change f (x - ((PadicInt.toZMod x).val : ℤ_[p])) = 0 at h
  simpa only [map_sub, map_natCast, sub_eq_zero] using h

/-- No choice of p-adic scalar action remains on a characteristic-p field. -/
theorem padicHom_unique (f g : ℤ_[p] →+* k) : f = g := by
  ext x
  rw [padicHom_apply p k f, padicHom_apply p k g]

variable [Finite k]

/-- The residue isomorphism respects the originally specified p-adic scalar action. -/
def residueAlgEquiv [Algebra ℤ_[p] k] :
    IsLocalRing.ResidueField (WittVector p k) ≃ₐ[ℤ_[p]] k :=
  { residueEquiv p k with
    commutes' := fun x ↦ DFunLike.congr_fun
      (padicHom_unique p k
        ((residueEquiv p k).toRingHom.comp (algebraMap ℤ_[p] _)) (algebraMap ℤ_[p] k)) x }

/-- The complete mixed-characteristic base, with its actual adic topology. -/
def coefficientObject : ProartinianCat (WittVector p k) := ProartinianCat.self

/-- The topology on this coefficient object is the p-adic topology. -/
theorem coefficientObject_topology :
    (coefficientObject p k).topologicalSpace =
      (Ideal.span {(p : WittVector p k)}).adicTopology := by
  change (IsLocalRing.maximalIdeal (WittVector p k)).adicTopology = _
  rw [maximalIdeal_eq]

end Deformation.WittCoefficients
