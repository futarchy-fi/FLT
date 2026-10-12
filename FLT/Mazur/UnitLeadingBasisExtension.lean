/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Basis.Prod

/-!
# Extending a basis by a specified unit-leading vector

For an exact sequence with scalar quotient, any chosen vector of coefficient
one extends the kernel basis. This retains the vector itself, including when
it is a product of previously constructed sections.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.UnitLeadingBasisExtension
open Module

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N] (f : M →ₗ[R] N) (g : N →ₗ[R] R)
  (hf : Function.Injective f) (hex : Function.Exact f g)
  (v : N) (hv : g v = 1)

/-- The original inclusion plus the specified vector, with its scalar coefficient. -/
def assemble : M × R →ₗ[R] N :=
  f.comp (LinearMap.fst R M R) + (LinearMap.id.smulRight v).comp (LinearMap.snd R M R)

include hex hv in
/-- Applying the quotient to the assembly recovers its scalar coordinate. -/
theorem assemble_leading (p : M × R) : g (assemble f v p) = p.2 := by
  change g (f p.1 + p.2 • v) = p.2
  rw [map_add, hex.apply_apply_eq_zero, map_smul, hv, smul_eq_mul, mul_one, zero_add]

include hf hex hv in
/-- Exactness and coefficient one make the original assembly bijective. -/
theorem assemble_bijective : Function.Bijective (assemble f v) := by
  constructor
  · intro p q hpq
    have h₂ : p.2 = q.2 := by
      simpa only [assemble_leading f g hex v hv] using congrArg g hpq
    apply Prod.ext (hf ?_) h₂
    change f p.1 + p.2 • v = f q.1 + q.2 • v at hpq
    rw [h₂] at hpq
    exact add_right_cancel hpq
  · intro z
    obtain ⟨x, hx⟩ := (hex (z - g z • v)).mp (by
      rw [map_sub, map_smul, hv, smul_eq_mul, mul_one, sub_self])
    refine ⟨(x, g z), ?_⟩
    change f x + g z • v = z
    rw [hx, sub_add_cancel]

/-- The actual product decomposition with the chosen vector as its second column. -/
def equiv : (M × R) ≃ₗ[R] N := LinearEquiv.ofBijective (assemble f v)
  (assemble_bijective f g hf hex v hv)

/-- A kernel basis extended by the specified unit-leading vector. -/
def basis {ι : Type*} (b : Basis ι R M) : Basis (ι ⊕ Unit) R N :=
  (b.prod (Basis.singleton Unit R)).map (equiv f g hf hex v hv)

/-- Old basis vectors enter through the original inclusion. -/
theorem basis_old {ι : Type*} (b : Basis ι R M) (i : ι) :
    basis f g hf hex v hv b (Sum.inl i) = f (b i) := by
  rw [basis, Basis.map_apply, Basis.prod_apply]
  change f (b i) + (0 : R) • v = f (b i)
  rw [zero_smul, add_zero]

/-- The new basis vector is exactly the specified vector. -/
theorem basis_new {ι : Type*} (b : Basis ι R M) :
    basis f g hf hex v hv b (Sum.inr ()) = v := by
  rw [basis, Basis.map_apply, Basis.prod_apply]
  change f 0 + (Basis.singleton Unit R ()) • v = v
  rw [Basis.singleton_apply, map_zero, one_smul, zero_add]

/-- The last basis coordinate of every vector is its original leading coefficient. -/
theorem basis_repr_new {ι : Type*} (b : Basis ι R M) (z : N) :
    (basis f g hf hex v hv b).repr z (Sum.inr ()) = g z := by
  rw [basis, Basis.map_repr, LinearEquiv.trans_apply, Basis.prod_repr_inr, Basis.singleton_repr]
  change ((equiv f g hf hex v hv).symm z).2 = g z
  have h := assemble_leading f g hex v hv ((equiv f g hf hex v hv).symm z)
  exact h.symm.trans (congrArg g ((equiv f g hf hex v hv).apply_symm_apply z))

end FLT.Mazur.UnitLeadingBasisExtension
