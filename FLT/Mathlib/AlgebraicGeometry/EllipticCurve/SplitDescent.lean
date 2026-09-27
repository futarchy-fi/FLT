/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Aut
public import FLT.Mathlib.AlgebraicGeometry.EllipticCurve.GaloisDescent
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Henselian
/-!
# Descent of split multiplicative models

Hensel lifting splits the node polynomial over the local field in every residue
characteristic. Its rational roots detect the sign of a geometric isomorphism.
-/

@[expose] public section

open Polynomial IsLocalRing ValuativeRel

/-- A split separable nonconstant reduction supplies a root over a Henselian local ring. -/
theorem Polynomial.exists_root_of_splits_reduction
    {R : Type*} [CommRing R] [IsLocalRing R]
    [HenselianRing R (maximalIdeal R)] (f : R[X]) (hf : f.Monic)
    (hs : (f.map (residue R)).Splits) (hsep : (f.map (residue R)).Separable)
    (hd : (f.map (residue R)).degree ≠ 0) : ∃ a : R, f.IsRoot a := by
  obtain ⟨a, ha⟩ := hs.exists_eval_eq_zero hd
  obtain ⟨a₀, rfl⟩ := residue_surjective a
  have hd0 : (f.map (residue R)).derivative.eval (residue R a₀) ≠ 0 := by
    exact hsep.eval₂_derivative_ne_zero (RingHom.id _) (by simpa using ha)
  obtain ⟨b, hb, -⟩ := HenselianRing.is_henselian (I := maximalIdeal R) f hf a₀
    (by
      apply (residue_eq_zero_iff _).mp
      simpa only [eval_map, eval₂_at_apply] using ha)
    (by
      change IsUnit (residue R (f.derivative.eval a₀))
      apply isUnit_iff_ne_zero.mpr
      change (residue R) (f.derivative.eval a₀) ≠ 0
      simpa only [derivative_map, eval_map, eval₂_at_apply] using hd0)
  exact ⟨b, hb⟩

/-- The monicity assumption in Hensel lifting can be replaced by a unit leading coefficient. -/
theorem Polynomial.exists_root_of_splits_reduction_of_isUnit_leadingCoeff
    {R : Type*} [CommRing R] [IsLocalRing R]
    [HenselianRing R (maximalIdeal R)] (p : R[X]) (hu : IsUnit p.leadingCoeff)
    (hs : (p.map (residue R)).Splits) (hsep : (p.map (residue R)).Separable)
    (hd : (p.map (residue R)).degree ≠ 0) : ∃ a : R, p.IsRoot a := by
  let u := hu.unit
  let f := C (↑u⁻¹ : R) * p
  have hm : f.Monic := monic_C_mul_of_mul_leadingCoeff_eq_one (by simp [u])
  have hunit : IsUnit (residue R (↑u⁻¹ : R)) := u⁻¹.isUnit.map _
  have hfm : f.map (residue R) = C (residue R (↑u⁻¹ : R)) * p.map (residue R) := by
    simp only [f, Polynomial.map_mul, map_C]
  obtain ⟨a, ha⟩ := f.exists_root_of_splits_reduction hm
    (by rw [hfm]; exact (Splits.C _).mul hs)
    (by rw [hfm]; exact Separable.unit_mul (hunit.map C) hsep)
    (by rw [hfm, degree_C_mul hunit.ne_zero]; exact hd)
  refine ⟨a, ?_⟩
  have h : (↑u⁻¹ : R) * p.eval a = 0 := by simpa only [IsRoot, f, eval_mul, eval_C] using ha
  exact (u⁻¹.isUnit.mul_right_eq_zero).mp h

namespace WeierstrassCurve
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- A split multiplicative model has a rational root of its node polynomial. -/
theorem exists_root_nodePoly_of_hasSplitMultiplicativeReduction
    (E : WeierstrassCurve K) [E.HasSplitMultiplicativeReduction 𝒪[K]] :
    ∃ a : K, E.nodePoly.IsRoot a := by
  let : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  have : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  let W := E.integralModel 𝒪[K]
  have hc : IsUnit W.c₄ := (residue_ne_zero_iff_isUnit _).mp
    (E.residue_integralModel_c₄_ne_zero 𝒪[K])
  have hl : W.nodePoly.leadingCoeff = W.c₄ := by
    simpa only [nodePoly, sub_eq_add_neg, ← map_neg] using
      (leadingCoeff_quadratic (b := W.a₁ * W.c₄)
        (c := -(54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)) hc.ne_zero)
  obtain ⟨a, ha⟩ := W.nodePoly.exists_root_of_splits_reduction_of_isUnit_leadingCoeff
    (hl ▸ hc) HasSplitMultiplicativeReduction.splitMultiplicativeReduction
    (E.separable_nodePoly_map 𝒪[K])
    (degree_ne_of_natDegree_ne (by
      change (W.nodePoly.map (algebraMap 𝒪[K] (ResidueField 𝒪[K]))).natDegree ≠ 0
      rw [E.natDegree_nodePoly_map 𝒪[K]]; norm_num))
  refine ⟨algebraMap 𝒪[K] K a, ?_⟩
  have he : W.map (algebraMap 𝒪[K] K) = E := by
    ext <;> simp [W, integralModel_a₁_eq, integralModel_a₂_eq, integralModel_a₃_eq,
      integralModel_a₄_eq, integralModel_a₆_eq]
  rw [← he, map_nodePoly]
  simp only [IsRoot, eval_map, eval₂_at_apply, ha.eq_zero, map_zero]

/-- The node polynomial of a split multiplicative model splits over the local field. -/
theorem nodePoly_splits_of_hasSplitMultiplicativeReduction
    (E : WeierstrassCurve K) [E.HasSplitMultiplicativeReduction 𝒪[K]] :
    E.nodePoly.Splits := by
  obtain ⟨a, ha⟩ := E.exists_root_nodePoly_of_hasSplitMultiplicativeReduction
  have hc : E.c₄ ≠ 0 := by
    intro h
    have he := integralModel_c₄_eq 𝒪[K] E
    have hz : (E.integralModel 𝒪[K]).c₄ = 0 :=
      (IsFractionRing.injective 𝒪[K] K) (he.trans (h.trans (map_zero _).symm))
    exact E.residue_integralModel_c₄_ne_zero 𝒪[K] (by rw [hz, map_zero])
  apply Splits.of_natDegree_eq_two (x := a) _ ha
  simpa only [nodePoly, sub_eq_add_neg, ← map_neg] using
    (natDegree_quadratic (b := E.a₁ * E.c₄)
      (c := -(54 * E.b₆ - 3 * E.b₂ * E.b₄ + E.a₂ * E.c₄)) hc)
end WeierstrassCurve

/-- A root over an extension of a split polynomial is defined over the ground field. -/
theorem Polynomial.Splits.root_mem_range
    {K L : Type*} [Field K] [Field L] (f : K →+* L)
    {p : K[X]} (hs : p.Splits) (hp : p ≠ 0) {x : L}
    (hx : (p.map f).IsRoot x) : x ∈ Set.range f := by
  have hm := (mem_roots (map_ne_zero hp)).mpr hx
  rw [hs.roots_map_of_injective f.injective] at hm
  obtain ⟨a, -, ha⟩ := Multiset.mem_map.mp hm
  exact ⟨a, ha⟩

namespace WeierstrassCurve
variable {K : Type*} [Field K]

/-- Negation cannot fix a root of the node polynomial when its discriminant is nonzero. -/
theorem neg_nodePoly_root_ne_self (E : WeierstrassCurve K)
    (hc₄ : E.c₄ ≠ 0) (hc₆ : E.c₆ ≠ 0) {x : K} (hx : E.nodePoly.IsRoot x) :
    -x - E.a₁ ≠ x := by
  intro h
  have hr : E.c₄ * x ^ 2 + E.a₁ * E.c₄ * x -
      (54 * E.b₆ - 3 * E.b₂ * E.b₄ + E.a₂ * E.c₄) = 0 := by
    simpa [IsRoot, nodePoly] using hx
  have hd := E.splitPolynomial_discrim
  apply mul_ne_zero hc₄ hc₆
  linear_combination hd + 4 * E.c₄ * hr + E.c₄ ^ 2 * (2 * x + E.a₁) * h

/-- Changes of variables send roots of the target node polynomial to roots of the source. -/
theorem nodePoly_isRoot_of_smul (E : WeierstrassCurve K) (C : VariableChange K)
    {x : K} (hx : (C • E).nodePoly.IsRoot x) :
    E.nodePoly.IsRoot ((C.u : K) * x + C.s) := by
  rw [IsRoot, nodePoly_smul, eval_mul, eval_C, eval_comp] at hx
  simpa only [IsRoot, eval_add, eval_mul, eval_C, eval_X] using
    (mul_eq_zero.mp hx).resolve_left (pow_ne_zero _ C.u⁻¹.ne_zero)

/-- If both node polynomials split, every geometric isomorphism is Galois-fixed. -/
theorem map_variableChange_eq_of_nodePoly_splits
    (V W : WeierstrassCurve K) (hc₄ : V.c₄ ≠ 0) (hc₆ : V.c₆ ≠ 0)
    (hV : V.nodePoly.Splits) (hW : ∃ x : K, W.nodePoly.IsRoot x)
    (L : Type*) [Field L] [Algebra K L] (C : VariableChange L)
    (hC : C • V.baseChange L = W.baseChange L) (σ : L ≃ₐ[K] L) :
    C.map σ.toAlgHom.toRingHom = C := by
  let D := C.map σ.toAlgHom.toRingHom
  have hD : D • V.baseChange L = W.baseChange L := map_smul_baseChange_eq L σ hC
  have haut : (C⁻¹ * D) • V.baseChange L = V.baseChange L := by
    rw [mul_smul, hD, ← hC, inv_smul_smul]
  have h4 : (V.baseChange L).c₄ ≠ 0 := by
    simpa [baseChange] using (map_ne_zero_iff (algebraMap K L) (algebraMap K L).injective).mpr hc₄
  have h6 : (V.baseChange L).c₆ ≠ 0 := by
    simpa [baseChange] using (map_ne_zero_iff (algebraMap K L) (algebraMap K L).injective).mpr hc₆
  rcases (V.baseChange L).eq_one_or_eq_negVariableChange_of_smul_eq_of_c₄_ne_zero h4 h6 haut
      with hid | hneg
  · exact (inv_mul_eq_one.mp hid).symm
  obtain ⟨x, hx⟩ := hW
  let xL := algebraMap K L x
  let y := (C.u : L) * xL + C.s
  have hxL : (W.baseChange L).nodePoly.IsRoot xL := by
    rw [baseChange, map_nodePoly]
    simp only [IsRoot, xL, eval_map_apply, hx.eq_zero, map_zero]
  have hy : (V.baseChange L).nodePoly.IsRoot y :=
    nodePoly_isRoot_of_smul _ C (hC.symm ▸ hxL)
  have hp : V.nodePoly ≠ 0 := by
    intro hz
    have he := congrArg (fun p : K[X] ↦ p.coeff 2) hz
    exact hc₄ (by simpa [nodePoly] using he)
  obtain ⟨z, hz⟩ := hV.root_mem_range (algebraMap K L) hp
    (show (V.nodePoly.map (algebraMap K L)).IsRoot y by simpa [baseChange, map_nodePoly] using hy)
  have hyfix : σ y = y := by rw [← hz, AlgEquiv.commutes]
  have hDeq : D = C * (V.baseChange L).negVariableChange := by
    rw [← hneg, mul_inv_cancel_left]
  have hyD : σ y = (D.u : L) * xL + D.s := by
    simp only [y, map_add, map_mul]
    rw [show σ xL = xL from σ.commutes x]
    rfl
  have hswap : -y - (V.baseChange L).a₁ = y := by
    rw [hyD, hDeq] at hyfix
    simpa [VariableChange.mul_def, negVariableChange, y, sub_eq_add_neg, mul_neg,
      add_comm, add_left_comm, add_assoc] using hyfix
  exact False.elim ((V.baseChange L).neg_nodePoly_root_ne_self h4 h6 hy hswap)
end WeierstrassCurve

namespace WeierstrassCurve
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Multiplicative reduction forces the fourth invariant to be nonzero in the local field. -/
theorem c₄_ne_zero_of_hasMultiplicativeReduction
    (E : WeierstrassCurve K) [E.HasMultiplicativeReduction 𝒪[K]] : E.c₄ ≠ 0 := by
  have hc : IsUnit (E.integralModel 𝒪[K]).c₄ :=
    (residue_ne_zero_iff_isUnit _).mp (E.residue_integralModel_c₄_ne_zero 𝒪[K])
  rw [← integralModel_c₄_eq 𝒪[K] E]
  exact (hc.map (algebraMap 𝒪[K] K)).ne_zero

/-- Multiplicative reduction forces the sixth invariant to be nonzero in the local field. -/
theorem c₆_ne_zero_of_hasMultiplicativeReduction
    (E : WeierstrassCurve K) [E.HasMultiplicativeReduction 𝒪[K]] : E.c₆ ≠ 0 := by
  have hc : IsUnit (E.integralModel 𝒪[K]).c₆ :=
    (residue_ne_zero_iff_isUnit _).mp (E.residue_integralModel_c₆_ne_zero 𝒪[K])
  rw [← integralModel_c₆_eq 𝒪[K] E]
  exact (hc.map (algebraMap 𝒪[K] K)).ne_zero

/-- Every isomorphism between split multiplicative models is fixed by base-field automorphisms.
The argument uses rational node-polynomial roots and includes residue characteristics
two and three. -/
theorem map_variableChange_eq_of_hasSplitMultiplicativeReduction
    (V W : WeierstrassCurve K)
    [V.HasSplitMultiplicativeReduction 𝒪[K]] [W.HasSplitMultiplicativeReduction 𝒪[K]]
    (L : Type*) [Field L] [Algebra K L] (C : VariableChange L)
    (hC : C • V.baseChange L = W.baseChange L) (σ : L ≃ₐ[K] L) :
    C.map σ.toAlgHom.toRingHom = C :=
  map_variableChange_eq_of_nodePoly_splits V W V.c₄_ne_zero_of_hasMultiplicativeReduction
    V.c₆_ne_zero_of_hasMultiplicativeReduction V.nodePoly_splits_of_hasSplitMultiplicativeReduction
    W.exists_root_nodePoly_of_hasSplitMultiplicativeReduction L C hC σ

/-- An isomorphism between split multiplicative models over a Galois extension descends. -/
theorem exists_variableChange_of_hasSplitMultiplicativeReduction
    (V W : WeierstrassCurve K)
    [V.HasSplitMultiplicativeReduction 𝒪[K]] [W.HasSplitMultiplicativeReduction 𝒪[K]]
    (L : Type*) [Field L] [Algebra K L] [IsGalois K L]
    {C : VariableChange L} (hC : C • V.baseChange L = W.baseChange L) :
    ∃ C₀ : VariableChange K, C₀ • V = W :=
  exists_variableChange_of_galois_fixed L hC
    (map_variableChange_eq_of_hasSplitMultiplicativeReduction V W L C hC)
end WeierstrassCurve
