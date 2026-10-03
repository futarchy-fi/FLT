/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.FlatPadic
public import FLT.GaloisRepresentation.HardlyRamified.Defs
public import FLT.GroupScheme.RaynaudExtension
public import Mathlib.Algebra.Group.Shrink
public import Mathlib.Algebra.GroupWithZero.Action.TransferInstance

/-!
# Arbitrary-universe Actual finite-flat models of the hardly ramified torsion levels

Flatness provides each level over the original rational completion. The point
comparison retains its local Galois action, and the coefficient quotient gives
the killing exponent. Compatible maps and integral exactness are separate.
-/

@[expose] public noncomputable section
open scoped TensorProduct

namespace GaloisRepresentation.IsHardlyRamified
open ThreeAdicPlan

/-- Every actual p-power reduction has a finite-flat model killed by that same power. -/
theorem exists_torsion_flat_model_universes
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p)
    {R V : Type*} [CommRing R] [IsLocalRing R] [Algebra ℤ_[p] R]
    [Module.Finite ℤ_[p] R] [Module.Free ℤ_[p] R]
    [TopologicalSpace R] [IsTopologicalRing R] [IsModuleTopology ℤ_[p] R]
    [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    (hV : Module.rank R V = 2) {ρ : GaloisRep ℚ R V}
    (hρ : IsHardlyRamified hpodd hV ρ) (n : ℕ) :
    let v := (Fact.out : p.Prime).toHeightOneSpectrumRingOfIntegersRat
    let τ := (ρ.baseChange (R ⧸ Ideal.span {(p : R) ^ n})).toLocal v
    ∃ (X : FF (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ))
      (e : X.Points ≃+ τ.Space),
      (∀ (g : Field.absoluteGaloisGroup (v.adicCompletion ℚ)) (x : X.Points),
        e (g • x) = g • e x) ∧ ∀ x : X.Points, p ^ n • x = 0 := by
  let v := (Fact.out : p.Prime).toHeightOneSpectrumRingOfIntegersRat
  let A := R ⧸ Ideal.span {(p : R) ^ n}
  let τ := (ρ.baseChange A).toLocal v
  have hz : (p ^ n : A) = 0 := by
    have h : Ideal.Quotient.mk (Ideal.span {(p : R) ^ n}) ((p : R) ^ n) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    simpa only [map_pow, map_natCast] using h
  have hkill (x : A ⊗[R] V) : p ^ n • x = 0 := by
    rw [← Nat.cast_smul_eq_nsmul A, Nat.cast_pow, hz, zero_smul]
  have hflat := hρ.isFlat.cond (Ideal.span {(p : R) ^ n}) (PadicInt.isOpen_span_p_pow p R n)
  let : Finite τ.Space := hflat.finite _ _ _ _
  let e : Shrink.{0} τ.Space ≃+ τ.Space := Shrink.addEquiv
  let : DistribMulAction (Field.absoluteGaloisGroup (v.adicCompletion ℚ))
      (Shrink.{0} τ.Space) := e.distribMulAction _
  let q : τ.Space →+[Field.absoluteGaloisGroup (v.adicCompletion ℚ)] Shrink.{0} τ.Space :=
    { e.symm.toAddMonoidHom with
      map_smul' := by
        intro g x
        change e.symm (g • x) = e.symm (g • e (e.symm x))
        rw [e.apply_symm_apply] }
  have hs := hflat.map _ _ _ _ q e.symm.bijective
  rcases hs with ⟨H, hH, hHopf, hFF, hE, f, hf⟩
  let X : FF (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) := {
    CoordinateRing := H
    Points := Shrink.{0} τ.Space
    points := f
    points_bijective := hf }
  exact ⟨X, e, fun g x ↦ e.apply_symm_apply (g • e x),
    fun x ↦ e.injective ((map_nsmul e (p ^ n) x).trans
      ((hkill (e x)).trans e.map_zero.symm))⟩

end GaloisRepresentation.IsHardlyRamified
