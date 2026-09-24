/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluMap

/-!
# The kernel of a trivial torsion quotient

The kernel is a finite Galois-stable subgroup of geometric points, so its Vélu coefficient
sums descend. No torsion-dimension or torsion-cardinality theorem is used: positivity of the
exponent suffices for finiteness. The geometric assertions about the candidate curve and its
coordinate map remain separate obligations.
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

end WeierstrassCurve.Velu
