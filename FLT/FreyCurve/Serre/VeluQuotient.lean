/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluAdditivity
public import FLT.FreyCurve.Serre.VeluElliptic

/-!
# The kernel of a trivial torsion quotient

The kernel is a finite Galois-stable subgroup of geometric points, so its Vélu coefficient
sums descend. No torsion-dimension or torsion-cardinality theorem is used: positivity of the
exponent suffices for finiteness. For odd torsion, the affine coordinate equation is proved
by the Vélu identity, and the candidate is proved elliptic. Additivity of its coordinate map
remains a separate obligation.
-/

@[expose] public section

noncomputable section

open scoped WeierstrassCurve.Affine

namespace WeierstrassCurve.Velu

variable (E : WeierstrassCurve ℚ) (n : ℕ)
variable (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion n →ₗ[ZMod n] ZMod n)

/-- The kernel of a torsion quotient, viewed as a subgroup of all geometric points. -/
def torsionKernel : AddSubgroup (E⁄(AlgebraicClosure ℚ)).Point where
  carrier := {P | ∃ t, q t = 0 ∧ t.val = P}
  zero_mem' := ⟨0, map_zero q, rfl⟩
  add_mem' := by
    rintro P Q ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    exact ⟨s + t, by simp [hs, ht], rfl⟩
  neg_mem' := by
    rintro P ⟨t, ht, rfl⟩
    exact ⟨-t, by simp [ht], rfl⟩

/-- Membership in the geometric kernel is exactly membership in the image of `ker q`. -/
theorem mem_torsionKernel (P : (E⁄(AlgebraicClosure ℚ)).Point) :
    P ∈ torsionKernel E n q ↔ ∃ t, q t = 0 ∧ t.val = P := Iff.rfl

/-- Every point of the geometric kernel is killed by the torsion exponent. -/
theorem torsionKernel_killed (P : (E⁄(AlgebraicClosure ℚ)).Point)
    (hP : P ∈ torsionKernel E n q) : n • P = 0 := by
  obtain ⟨t, _, rfl⟩ := hP
  change n • t.val = 0
  simpa only [Submodule.mem_torsionBy_iff, natCast_zsmul] using t.property


/-- Odd torsion excludes nonzero kernel points fixed by negation. -/
theorem torsionKernel_ne_neg (hn : Odd n) (P : torsionKernel E n q) (hP : P ≠ 0) :
    P ≠ -P := by
  apply ne_neg_of_odd_nsmul hn hP
  apply Subtype.ext
  exact torsionKernel_killed E n q P.val P.property

/-- The coordinate sums for an odd torsion kernel satisfy the explicit candidate equation. -/
theorem torsionKernel_equation [Fintype (torsionKernel E n q)] (hn : Odd n)
    (P : (E⁄(AlgebraicClosure ℚ)).Point) (hP : P ∉ torsionKernel E n q) :
    (curve (E⁄(AlgebraicClosure ℚ)) (torsionKernel E n q)).toAffine.Equation
      (xMap (E⁄(AlgebraicClosure ℚ)) (torsionKernel E n q) P)
      (yMap (E⁄(AlgebraicClosure ℚ)) (torsionKernel E n q) P) :=
  equation_xMap_yMap_of_not_mem _ _ (torsionKernel_ne_neg E n q hn) P hP

/-- The descended Vélu candidate for an odd torsion kernel is elliptic. -/
theorem torsionQuotient_isElliptic [E.IsElliptic] [Fintype (torsionKernel E n q)]
    (hn : Odd n) (E' : WeierstrassCurve ℚ)
    (hcurve : E'.map (algebraMap ℚ (AlgebraicClosure ℚ)) =
      curve (E⁄(AlgebraicClosure ℚ)) (torsionKernel E n q)) : E'.IsElliptic := by
  let : (E⁄(AlgebraicClosure ℚ)).IsElliptic := by
    change (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).IsElliptic
    infer_instance
  have hd := curve_discr_ne_zero (E⁄(AlgebraicClosure ℚ)) (torsionKernel E n q)
    (torsionKernel_ne_neg E n q hn)
  refine ⟨isUnit_iff_ne_zero.mpr ?_⟩
  intro hz
  apply hd
  rw [← hcurve, map_Δ, hz, map_zero]

/-- The descended odd-kernel coordinate map lands on its elliptic target. -/
theorem torsionKernel_landing [E.IsElliptic] [Fintype (torsionKernel E n q)] (hn : Odd n)
    (E' : WeierstrassCurve ℚ)
    (hcurve : E'.map (algebraMap ℚ (AlgebraicClosure ℚ)) =
      curve (E⁄(AlgebraicClosure ℚ)) (torsionKernel E n q))
    (P : (E⁄(AlgebraicClosure ℚ)).Point) (hP : P ∉ torsionKernel E n q) :
    (E'⁄(AlgebraicClosure ℚ)).Nonsingular
      (xMap (E⁄(AlgebraicClosure ℚ)) (torsionKernel E n q) P)
      (yMap (E⁄(AlgebraicClosure ℚ)) (torsionKernel E n q) P) := by
  let := torsionQuotient_isElliptic E n q hn E' hcurve
  let : (E'⁄(AlgebraicClosure ℚ)).IsElliptic := by
    change (E'.map (algebraMap ℚ (AlgebraicClosure ℚ))).IsElliptic
    infer_instance
  apply Affine.equation_iff_nonsingular.mp
  change (E'.map (algebraMap ℚ (AlgebraicClosure ℚ))).toAffine.Equation _ _
  rw [hcurve]
  exact torsionKernel_equation E n q hn P hP

/-- The kernel of a quotient of positive-order torsion is finite.
This uses the proved finiteness theorem, not the admitted torsion-cardinality theorem. -/
theorem torsionKernel_finite [E.IsElliptic] (hn : 0 < n) : Finite (torsionKernel E n q) := by
  let := (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).n_torsion_finite hn
  let f : q.ker → torsionKernel E n q := fun t ↦ ⟨t.val.val, t.val, t.property, rfl⟩
  apply Finite.of_surjective f
  rintro ⟨P, t, ht, rfl⟩
  exact ⟨⟨t, ht⟩, rfl⟩

/-- A Galois-invariant quotient has a Galois-stable geometric kernel. -/
theorem torsionKernel_stable
    (hfixed : ∀ g t, q (E.torsionGaloisRepresentation n g t) = q t)
    (g : Field.absoluteGaloisGroup ℚ) (P : (E⁄(AlgebraicClosure ℚ)).Point)
    (hP : P ∈ torsionKernel E n q) :
    Affine.Point.map (W' := E) g.toAlgHom P ∈ torsionKernel E n q := by
  obtain ⟨t, ht, rfl⟩ := hP
  exact ⟨E.torsionGaloisRepresentation n g t, (hfixed g t).trans ht, rfl⟩

/-- The explicit Vélu equation attached to a trivial torsion quotient descends to `ℚ`.
Ellipticity of the descended equation is not asserted. -/
theorem exists_torsionQuotient_curve [E.IsElliptic] (hn : 0 < n)
    (hfixed : ∀ g t, q (E.torsionGaloisRepresentation n g t) = q t) :
    letI : Fintype (torsionKernel E n q) :=
      @Fintype.ofFinite _ (torsionKernel_finite E n q hn)
    ∃ E' : WeierstrassCurve ℚ, E'.map (algebraMap ℚ (AlgebraicClosure ℚ)) =
      curve (E⁄(AlgebraicClosure ℚ)) (torsionKernel E n q) := by
  let : Fintype (torsionKernel E n q) :=
    @Fintype.ofFinite _ (torsionKernel_finite E n q hn)
  exact exists_curve E (torsionKernel E n q) (torsionKernel_stable E n q hfixed)

/-- A Galois-invariant quotient of positive odd torsion has an elliptic Vélu candidate over ℚ. -/
theorem exists_torsionQuotient_elliptic [E.IsElliptic] (hn : 0 < n) (hodd : Odd n)
    (hfixed : ∀ g t, q (E.torsionGaloisRepresentation n g t) = q t) :
    letI : Fintype (torsionKernel E n q) :=
      @Fintype.ofFinite _ (torsionKernel_finite E n q hn)
    ∃ E' : WeierstrassCurve ℚ, E'.IsElliptic ∧
      E'.map (algebraMap ℚ (AlgebraicClosure ℚ)) =
        curve (E⁄(AlgebraicClosure ℚ)) (torsionKernel E n q) := by
  let : Fintype (torsionKernel E n q) :=
    @Fintype.ofFinite _ (torsionKernel_finite E n q hn)
  obtain ⟨E', hcurve⟩ := exists_torsionQuotient_curve E n q hn hfixed
  exact ⟨E', torsionQuotient_isElliptic E n q hodd E' hcurve, hcurve⟩

/-- Landing and additivity of the explicit Vélu map suffice for the rational maps in Serre's
quotient branch. The kernel and Galois compatibility are proved, rather than supplied as
additional geometric hypotheses. Ellipticity of the target remains a separate obligation. -/
theorem rational_maps_of_velu [Fintype (torsionKernel E n q)]
    (hq : Function.Surjective q)
    (hfixed : ∀ g t, q (E.torsionGaloisRepresentation n g t) = q t)
    (E' : WeierstrassCurve ℚ)
    (h : ∀ P, P ∉ torsionKernel E n q → (E'⁄(AlgebraicClosure ℚ)).Nonsingular
      (xMap (E⁄(AlgebraicClosure ℚ)) (torsionKernel E n q) P)
      (yMap (E⁄(AlgebraicClosure ℚ)) (torsionKernel E n q) P))
    (hadd : ∀ P Q,
      pointMap (E⁄(AlgebraicClosure ℚ)) (torsionKernel E n q) (E'⁄(AlgebraicClosure ℚ)) h
          (P + Q) =
        pointMap (E⁄(AlgebraicClosure ℚ)) (torsionKernel E n q) (E'⁄(AlgebraicClosure ℚ)) h P +
        pointMap (E⁄(AlgebraicClosure ℚ)) (torsionKernel E n q) (E'⁄(AlgebraicClosure ℚ)) h Q) :
    ∃ (φ : (E⁄ℚ).Point →+ (E'⁄ℚ).Point) (f : ZMod n →+ (E'⁄ℚ).Point),
      (∀ a, φ a = 0 → n • a = 0) ∧ Function.Injective f := by
  let ψ : (E⁄(AlgebraicClosure ℚ)).Point →+ (E'⁄(AlgebraicClosure ℚ)).Point := {
    toFun := pointMap (E⁄(AlgebraicClosure ℚ)) (torsionKernel E n q)
      (E'⁄(AlgebraicClosure ℚ)) h
    map_zero' := pointMap_zero _ _ _ h
    map_add' := hadd }
  have hψ (g : Field.absoluteGaloisGroup ℚ) (P : (E⁄(AlgebraicClosure ℚ)).Point) :
      ψ (Affine.Point.map (W' := E) g.toAlgHom P) =
        Affine.Point.map (W' := E') g.toAlgHom (ψ P) :=
    pointMap_map E (torsionKernel E n q) E' h (torsionKernel_stable E n q hfixed) g P
  have hker (P : (E⁄(AlgebraicClosure ℚ)).Point) :
      ψ P = 0 ↔ ∃ t, q t = 0 ∧ t.val = P :=
    (pointMap_eq_zero_iff _ _ _ h P).trans (mem_torsionKernel E n q P)
  obtain ⟨φ, f, hφ, hf, _, _⟩ :=
    rational_maps_of_trivial_quotient_of_geometric_map E E' n q hq hfixed ψ hψ hker
  exact ⟨φ, f, hφ, hf⟩

/-- In the odd-torsion branch, only additivity away from the kernel remains geometric input.
Target ellipticity, the coordinate equation, exceptional addition cases, and descent are proved. -/
theorem rational_maps_of_odd_velu [E.IsElliptic] [Fintype (torsionKernel E n q)]
    (hn : Odd n) (hq : Function.Surjective q)
    (hfixed : ∀ g t, q (E.torsionGaloisRepresentation n g t) = q t)
    (E' : WeierstrassCurve ℚ)
    (hcurve : E'.map (algebraMap ℚ (AlgebraicClosure ℚ)) =
      curve (E⁄(AlgebraicClosure ℚ)) (torsionKernel E n q))
    (hadd : ∀ P Q, P ∉ torsionKernel E n q → Q ∉ torsionKernel E n q →
      P + Q ∉ torsionKernel E n q →
      pointMap (E⁄(AlgebraicClosure ℚ)) (torsionKernel E n q) (E'⁄(AlgebraicClosure ℚ))
          (torsionKernel_landing E n q hn E' hcurve) (P + Q) =
        pointMap (E⁄(AlgebraicClosure ℚ)) (torsionKernel E n q) (E'⁄(AlgebraicClosure ℚ))
            (torsionKernel_landing E n q hn E' hcurve) P +
          pointMap (E⁄(AlgebraicClosure ℚ)) (torsionKernel E n q) (E'⁄(AlgebraicClosure ℚ))
            (torsionKernel_landing E n q hn E' hcurve) Q) :
    E'.IsElliptic ∧
      ∃ (φ : (E⁄ℚ).Point →+ (E'⁄ℚ).Point) (f : ZMod n →+ (E'⁄ℚ).Point),
        (∀ a, φ a = 0 → n • a = 0) ∧ Function.Injective f :=
  ⟨torsionQuotient_isElliptic E n q hn E' hcurve,
    rational_maps_of_velu E n q hq hfixed E'
      (torsionKernel_landing E n q hn E' hcurve)
      (pointMap_add_of_add_off_kernel _ _ _
        (torsionKernel_landing E n q hn E' hcurve)
        (by change (E'.map _).a₁ = _; rw [hcurve]; rfl)
        (by change (E'.map _).a₃ = _; rw [hcurve]; rfl)
        hadd)⟩

end WeierstrassCurve.Velu
