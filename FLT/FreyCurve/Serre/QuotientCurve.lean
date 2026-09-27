/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluHom
public import FLT.FreyCurve.Serre.VeluQuotient

/-!
# Elliptic quotients with rational torsion

Vélu's map for a finite odd torsion kernel is additive, has the exact kernel,
and commutes with Galois. Descending its target and the image of a trivial torsion
quotient gives the rational maps required by Serre's argument.

The prime case assumes `p ≠ 2`, as holds for the Frey application with `p ≥ 5`.
-/

@[expose] public section

open scoped WeierstrassCurve.Affine
namespace WeierstrassCurve

/-- A trivial quotient of positive odd geometric torsion gives rational torsion
on an elliptic quotient, with a rational map whose kernel is killed by the exponent. -/
theorem quotient_curve_of_trivial_odd_quotient
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (n : ℕ) (hn : 0 < n) (hodd : Odd n)
    (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion n →ₗ[ZMod n] ZMod n)
    (hq : Function.Surjective q)
    (hfixed : ∀ g v, q (E.torsionGaloisRepresentation n g v) = q v) :
    ∃ (E' : WeierstrassCurve ℚ) (_ : E'.IsElliptic),
      ∃ (φ : (E⁄ℚ).Point →+ (E'⁄ℚ).Point) (f : ZMod n →+ (E'⁄ℚ).Point),
        (∀ a, φ a = 0 → n • a = 0) ∧ Function.Injective f := by
  classical
  let : (E⁄(AlgebraicClosure ℚ)).IsElliptic := by
    change (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).IsElliptic
    infer_instance
  let : Fintype (Velu.torsionKernel E n q) :=
    @Fintype.ofFinite _ (Velu.torsionKernel_finite E n q hn)
  obtain ⟨E', hcurve⟩ := Velu.exists_torsionQuotient_curve E n q hn hfixed
  have hadd := Velu.pointMap_add_of_curve_eq (E⁄(AlgebraicClosure ℚ))
    (Velu.torsionKernel E n q) (Velu.torsionKernel_ne_neg E n q hodd)
    (E'.map (algebraMap ℚ (AlgebraicClosure ℚ))) hcurve
    (Velu.torsionKernel_landing E n q hodd E' hcurve)
  obtain ⟨hE', hm⟩ := Velu.rational_maps_of_odd_velu E n q hodd hq hfixed E' hcurve
    (fun P Q _ _ _ => hadd P Q)
  exact ⟨E', hE', hm⟩

/-- The odd-prime trivial-quotient leaf in Serre's reducible-representation argument. -/
theorem quotient_curve_of_trivial_quotient
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime]
    (hp : 0 < p) (hp2 : p ≠ 2)
    (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →ₗ[ZMod p] ZMod p)
    (hq : Function.Surjective q)
    (hfixed : ∀ g v, q (E.galoisRep p hp g v) = q v) :
    ∃ (E' : WeierstrassCurve ℚ) (hE' : E'.IsElliptic),
      letI : E'.IsElliptic := hE'
      ∃ (φ : (E⁄ℚ).Point →+ (E'⁄ℚ).Point) (f : ZMod p →+ (E'⁄ℚ).Point),
        (∀ a, φ a = 0 → p • a = 0) ∧ Function.Injective f := by
  exact quotient_curve_of_trivial_odd_quotient E p hp
    (Nat.Prime.odd_of_ne_two Fact.out hp2) q hq hfixed

end WeierstrassCurve
