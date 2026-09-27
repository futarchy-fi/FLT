/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.FixedLineDescent

/-!
# Point-level consequences of a quotient isogeny

These lemmas isolate the algebra and descent needed for the trivial-quotient branch of
Serre's argument. Constructing the quotient elliptic curve and its geometric point map
remains a separate geometric input.
-/

@[expose] public section

namespace AddMonoidHom

/-- A map with the same kernel as a surjection induces an injection from its target. -/
theorem exists_injective_factor_of_ker_eq {A B C : Type*}
    [AddGroup A] [AddGroup B] [AddGroup C]
    (q : A →+ B) (hq : Function.Surjective q) (f : A →+ C)
    (hker : q.ker = f.ker) :
    ∃ j : B →+ C, Function.Injective j ∧ ∀ a, j (q a) = f a := by
  let j := q.liftOfSurjective hq ⟨f, hker.le⟩
  have hj (a : A) : j (q a) = f a :=
    q.liftOfRightInverse_comp_apply _ _ _ a
  refine ⟨j, (injective_iff_map_eq_zero j).mpr ?_, hj⟩
  intro b hb
  obtain ⟨a, rfl⟩ := hq b
  have ha : a ∈ f.ker := (hj a).symm.trans hb
  exact show a ∈ q.ker from hker.symm ▸ ha

end AddMonoidHom

namespace WeierstrassCurve

/-! ### A finite-sum descent lemma used by the Vélu construction -/

open scoped BigOperators

/--
If a finite family of coefficients is permuted by a field automorphism, its sum is fixed.

This is the algebraic core of the Galois-invariance step in Vélu's construction: once a
Galois-stable kernel supplies the permutation `e` and the summand is shown to be equivariant,
the resulting coefficient lies in the ground field.  The lemma is deliberately independent of
elliptic-curve coordinates so it can also be reused for the general Weierstrass formulas.
-/
theorem galois_fixed_sum_of_equiv {K L ι : Type*} [CommSemiring K] [CommRing L] [Algebra K L]
    [Fintype ι] (σ : L ≃ₐ[K] L) (e : ι ≃ ι) (f : ι → L)
    (hσ : ∀ i, σ (f i) = f (e i)) :
    σ (∑ i, f i) = ∑ i, f i := by
  rw [map_sum]
  calc
    ∑ i, σ (f i) = ∑ i, f (e i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hσ i
    _ = ∑ i, f i := e.sum_comp f

end WeierstrassCurve

open scoped WeierstrassCurve.Affine

namespace WeierstrassCurve

/-- An equivariant map on geometric torsion with kernel equal to that of a trivial
quotient embeds that quotient into rational points of the target curve. No existence
of a quotient curve or isogeny is asserted here. -/
theorem rational_torsion_of_trivial_quotient_image
    (E E' : WeierstrassCurve ℚ) (n : ℕ)
    (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion n →ₗ[ZMod n] ZMod n)
    (hq : Function.Surjective q)
    (hfixed : ∀ g v, q (E.torsionGaloisRepresentation n g v) = q v)
    (ψ : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion n →+
      (E'⁄(AlgebraicClosure ℚ)).Point)
    (hψ : ∀ g v, ψ (E.torsionGaloisRepresentation n g v) =
      Affine.Point.map (W' := E') g.toAlgHom (ψ v))
    (hker : q.toAddMonoidHom.ker = ψ.ker) :
    ∃ f : ZMod n →+ (E'⁄ℚ).Point, Function.Injective f ∧
      ∀ v, Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) (f (q v)) = ψ v := by
  obtain ⟨j, hj, hjq⟩ := q.toAddMonoidHom.exists_injective_factor_of_ker_eq hq ψ hker
  change ∀ v, j (q v) = ψ v at hjq
  have hjfixed (g : Field.absoluteGaloisGroup ℚ) (x : ZMod n) :
      Affine.Point.map (W' := E') g.toAlgHom (j x) = j x := by
    obtain ⟨v, rfl⟩ := hq x
    rw [hjq, ← hψ, ← hjq, hfixed, hjq]
  obtain ⟨f, hf⟩ := E'.exists_addHom_of_galois_fixed j hjfixed
  refine ⟨f, fun a b hab ↦ hj ?_, fun v ↦ (hf (q v)).trans (hjq v)⟩
  exact (hf a).symm.trans
    ((congrArg (Affine.Point.baseChange ℚ (AlgebraicClosure ℚ)) hab).trans (hf b))

/-- A geometric point homomorphism with kernel exactly the kernel of a trivial torsion
quotient supplies both rational maps required by Serre's quotient branch.

The target curve and geometric map are hypotheses: the missing quotient-isogeny existence
theorem must construct them. The conclusion uses neither surjectivity on rational points
nor a dual isogeny. -/
theorem rational_maps_of_trivial_quotient_of_geometric_map
    (E E' : WeierstrassCurve ℚ) (n : ℕ)
    (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion n →ₗ[ZMod n] ZMod n)
    (hq : Function.Surjective q)
    (hfixed : ∀ g v, q (E.torsionGaloisRepresentation n g v) = q v)
    (ψ : (E⁄(AlgebraicClosure ℚ)).Point →+ (E'⁄(AlgebraicClosure ℚ)).Point)
    (hψ : ∀ (g : Field.absoluteGaloisGroup ℚ) v,
      ψ (Affine.Point.map (W' := E) g.toAlgHom v) =
        Affine.Point.map (W' := E') g.toAlgHom (ψ v))
    (hker : ∀ v, ψ v = 0 ↔
      ∃ t : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion n,
        q t = 0 ∧ t.val = v) :
    ∃ (φ : (E⁄ℚ).Point →+ (E'⁄ℚ).Point) (f : ZMod n →+ (E'⁄ℚ).Point),
      (∀ a, φ a = 0 → n • a = 0) ∧ Function.Injective f ∧
      (∀ a, Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) (φ a) =
        ψ (Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) a)) ∧
      (∀ t, Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) (f (q t)) = ψ t.val) := by
  let ψt := ψ.comp
    (Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ)).Point n).subtype.toAddMonoidHom
  have hkert : q.toAddMonoidHom.ker = ψt.ker := by
    ext t
    change q t = 0 ↔ ψ t.val = 0
    constructor
    · intro ht
      exact (hker t.val).mpr ⟨t, ht, rfl⟩
    · intro ht
      obtain ⟨s, hs, hst⟩ := (hker t.val).mp ht
      exact (congrArg q (Subtype.ext hst)).symm.trans hs
  obtain ⟨f, hf, hfq⟩ := rational_torsion_of_trivial_quotient_image E E' n q hq hfixed
    ψt (fun g t ↦ hψ g t.val) hkert
  let ψ₀ := ψ.comp (Affine.Point.baseChange ℚ (AlgebraicClosure ℚ))
  have hψ₀ (g : Field.absoluteGaloisGroup ℚ) (a : (E⁄ℚ).Point) :
      Affine.Point.map (W' := E') g.toAlgHom (ψ₀ a) = ψ₀ a := by
    change Affine.Point.map (W' := E') g.toAlgHom
      (ψ (Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) a)) = _
    rw [← hψ, Affine.Point.map_baseChange]
    rfl
  obtain ⟨φ, hφ⟩ := E'.exists_addHom_of_galois_fixed ψ₀ hψ₀
  change ∀ a, Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) (φ a) =
    ψ (Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) a) at hφ
  refine ⟨φ, f, ?_, hf, hφ, hfq⟩
  intro a ha
  have hψa : ψ (Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) a) = 0 := by
    rw [← hφ, ha, map_zero]
  obtain ⟨t, _, ht⟩ := (hker _).mp hψa
  apply Affine.Point.map_injective (W' := E.toAffine)
    (Algebra.ofId ℚ (AlgebraicClosure ℚ))
  change Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) (n • a) =
    Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) 0
  rw [map_nsmul, map_zero, ← ht]
  change n • t.val = 0
  simpa only [Submodule.mem_torsionBy_iff, natCast_zsmul] using t.property

end WeierstrassCurve
