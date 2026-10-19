/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.QuotientCurveEquation

/-!
# The geometric coordinate homomorphism of the descended quotient

Retain the actual Vélu coordinate map, its exact kernel, and the two base-change
identities that identify the descended rational maps. This is point-level data;
it does not assert the existence of a scheme morphism or a dual isogeny.
-/

@[expose] public section

noncomputable section

open scoped WeierstrassCurve.Affine

namespace WeierstrassCurve.Velu

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (n : ℕ) (hn : 0 < n)
variable (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion n →ₗ[ZMod n] ZMod n)
variable (hodd : Odd n) (E' : WeierstrassCurve ℚ)
variable (hcurve : TorsionQuotientEquation E n hn q E')

/-- The homomorphism given by the Vélu coordinate sums on the descended target. -/
def torsionQuotientPointHom : (E⁄(AlgebraicClosure ℚ)).Point →+
    (E'⁄(AlgebraicClosure ℚ)).Point := by
  classical
  let _ : (E⁄(AlgebraicClosure ℚ)).IsElliptic := by
    change (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).IsElliptic
    infer_instance
  let _ : Fintype (torsionKernel E n q) :=
    @Fintype.ofFinite _ (torsionKernel_finite E n q hn)
  let h := torsionKernel_landing E n q hodd E' hcurve
  exact {
    toFun := pointMap (E⁄(AlgebraicClosure ℚ)) (torsionKernel E n q)
      (E'⁄(AlgebraicClosure ℚ)) h
    map_zero' := pointMap_zero _ _ _ h
    map_add' := pointMap_add_of_curve_eq _ _ (torsionKernel_ne_neg E n q hodd)
      (E'.map (algebraMap ℚ (AlgebraicClosure ℚ))) hcurve h }

/-- The coordinate homomorphism kills exactly the geometric kernel of `q`. -/
theorem torsionQuotientPointHom_eq_zero_iff (P : (E⁄(AlgebraicClosure ℚ)).Point) :
    torsionQuotientPointHom E n hn q hodd E' hcurve P = 0 ↔
      P ∈ torsionKernel E n q := by
  classical
  let _ : Fintype (torsionKernel E n q) :=
    @Fintype.ofFinite _ (torsionKernel_finite E n q hn)
  exact pointMap_eq_zero_iff _ _ _ (torsionKernel_landing E n q hodd E' hcurve) P

/-- The retained coordinate homomorphism is Galois-equivariant. -/
theorem torsionQuotientPointHom_map
    (hfixed : ∀ g t, q (E.torsionGaloisRepresentation n g t) = q t)
    (g : Field.absoluteGaloisGroup ℚ) (P : (E⁄(AlgebraicClosure ℚ)).Point) :
    torsionQuotientPointHom E n hn q hodd E' hcurve
        (Affine.Point.map (W' := E) g.toAlgHom P) =
      Affine.Point.map (W' := E') g.toAlgHom
        (torsionQuotientPointHom E n hn q hodd E' hcurve P) := by
  classical
  let _ : Fintype (torsionKernel E n q) :=
    @Fintype.ofFinite _ (torsionKernel_finite E n q hn)
  exact pointMap_map E (torsionKernel E n q) E'
    (torsionKernel_landing E n q hodd E' hcurve) (torsionKernel_stable E n q hfixed) g P

/-- Rational maps descend from the specified coordinate homomorphism, retaining both squares. -/
theorem rational_maps_of_torsionQuotientEquation (hq : Function.Surjective q)
    (hfixed : ∀ g t, q (E.torsionGaloisRepresentation n g t) = q t) :
    ∃ (φ : (E⁄ℚ).Point →+ (E'⁄ℚ).Point) (f : ZMod n →+ (E'⁄ℚ).Point),
      (∀ a, φ a = 0 → n • a = 0) ∧ Function.Injective f ∧
      (∀ a, Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) (φ a) =
        torsionQuotientPointHom E n hn q hodd E' hcurve
          (Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) a)) ∧
      (∀ t, Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) (f (q t)) =
        torsionQuotientPointHom E n hn q hodd E' hcurve t.val) := by
  apply rational_maps_of_trivial_quotient_of_geometric_map E E' n q hq hfixed
    (torsionQuotientPointHom E n hn q hodd E' hcurve)
    (torsionQuotientPointHom_map E n hn q hodd E' hcurve hfixed)
  intro P
  exact (torsionQuotientPointHom_eq_zero_iff E n hn q hodd E' hcurve P).trans
    (mem_torsionKernel E n q P)

end WeierstrassCurve.Velu
