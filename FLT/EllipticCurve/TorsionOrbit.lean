/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.Torsion
public import Mathlib.FieldTheory.Normal.Basic

/-!
# Torsion orbits and stable lines

Galois transitivity on inverse x-coordinates makes every nonzero prime-torsion
point conjugate up to sign. A stable line would then contain the entire torsion
group, contradicting its cardinality. The cardinality theorem is an existing
repository admission.
-/

@[expose] public section

open Polynomial
namespace WeierstrassCurve
variable {K : Type*} [Field K] [CharZero K]
/-- Classical equality for geometric point coordinates. -/
noncomputable local instance torsionOrbitDecidableEq (α : Type*) : DecidableEq α :=
  Classical.typeDecidableEq α
local notation "Ω" => AlgebraicClosure K

/-- An irreducible polynomial vanishing at all inverse torsion x-coordinates
precludes a Galois-stable prime-order line. This uses the existing
`n_torsion_card` theorem to compare the line with the full torsion group. -/
theorem no_stableLine_of_irreducible_inverseX (E : WeierstrassCurve K) [E.IsElliptic]
    (p : ℕ) (hp : p.Prime) (f : K[X]) (hf : Irreducible f)
    (hroot : ∀ (x y : Ω) (h : (E.map (algebraMap K Ω)).toAffine.Nonsingular x y),
      p • Affine.Point.some x y h = 0 → aeval x⁻¹ f = 0) :
    letI : Fact p.Prime := ⟨hp⟩
    ¬ ∃ i : ZMod p →ₗ[ZMod p] (E.map (algebraMap K Ω)).nTorsion p,
      Function.Injective i ∧ ∀ σ : Field.absoluteGaloisGroup K,
        ∃ a : ZMod p, E.galoisRep p hp.pos σ (i 1) = i a := by
  let : Fact p.Prime := ⟨hp⟩
  rintro ⟨i, hinj, hstable⟩
  have hnonzero : i 1 ≠ 0 := fun he => one_ne_zero (hinj (he.trans i.map_zero.symm))
  have ht (P : (E.map (algebraMap K Ω)).nTorsion p) : p • P.val = 0 := by
    simpa only [Submodule.mem_torsionBy_iff, natCast_zsmul] using P.property
  have hsurj : Function.Surjective i := by
    cases hP : (i 1).val with
    | zero => exact (hnonzero (Subtype.ext hP)).elim
    | some x y h =>
      have hx : aeval x⁻¹ f = 0 := hroot x y h (by
        have hh := ht (i 1)
        rw [hP] at hh
        exact hh)
      intro Q
      cases hQ : Q.val with
      | zero => exact ⟨0, i.map_zero.trans (Subtype.ext hQ).symm⟩
      | some u v h' =>
        have hu : aeval u⁻¹ f = 0 := hroot u v h' (by
          have hh := ht Q
          rw [hQ] at hh
          exact hh)
        have hm : minpoly K u⁻¹ = minpoly K x⁻¹ :=
          (minpoly.eq_of_irreducible hf hu).symm.trans (minpoly.eq_of_irreducible hf hx)
        obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (E := Ω)).mp hm
        have hxu : σ x = u := by
          have hh := congrArg Inv.inv hσ
          simpa only [AlgEquiv.smul_def, map_inv₀, inv_inv] using hh
        obtain ⟨a, ha⟩ := hstable σ
        have hσP := congrArg (Affine.Point.map (W' := E) σ.toAlgHom) hP
        have hσh := (E.toAffine.baseChange_nonsingular (f := σ.toAlgHom) σ.injective x y).mpr h
        change (E.galoisRep p hp.pos σ (i 1)).val = Affine.Point.some (σ x) (σ y) hσh at hσP
        have hpoints := (Affine.Point.X_eq_iff (h₁ := hσh) (h₂ := h')).mp hxu
        rcases hpoints with he | he
        · refine ⟨a, Subtype.ext ?_⟩
          exact (congrArg Subtype.val ha).symm.trans (hσP.trans (he.trans hQ.symm))
        · have he' : i a = -Q := by
            apply Subtype.ext
            exact (congrArg Subtype.val ha).symm.trans
              (hσP.trans (he.trans (congrArg Neg.neg hQ.symm)))
          exact ⟨-a, by rw [map_neg, he', neg_neg]⟩
  have hc := Nat.card_congr (Equiv.ofBijective i ⟨hinj, hsurj⟩)
  have hT := (E.map (algebraMap K Ω)).n_torsion_card (n := p) (by exact_mod_cast hp.ne_zero)
  have hz : Nat.card (ZMod p) = p := by simp
  rw [hz, hT] at hc
  nlinarith [hp.two_le]
end WeierstrassCurve

