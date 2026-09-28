/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.GlobalModel
public import FLT.GroupScheme.RaynaudExtensionExists
public import FLT.GroupScheme.RaynaudInversionBasis
public import Mathlib.LinearAlgebra.Dimension.Localization

/-!
# Classification of order-three models over the three-adic integers

The geometric generic points bound each inversion eigenspace of the augmentation
ideal by rank one. The integral inversion projectors split the coordinate module,
so both eigenspaces are free of rank one. Their generators give an inversion basis;
the Hopf identities then make it an Oort–Tate power basis.

No classification or presentation hypothesis is imposed on the model.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ThreeAdicPlan.RankThree

/-- Every element of a group of order three is zero or one of a pair of opposites. -/
lemma three_cases {G : Type} [AddCommGroup G] [Finite G] (hcard : Nat.card G = 3)
    (p : G) (hp : p ≠ 0) (q : G) : q = 0 ∨ q = p ∨ q = -p := by
  classical
  let := Fintype.ofFinite G
  have hp3 : 3 • p = 0 := by simpa only [hcard] using (card_nsmul_eq_zero' (x := p))
  have hpn : p ≠ -p := by
    intro h
    have hp2 : 2 • p = 0 := by simpa [two_nsmul] using congrArg (· + p) h
    apply hp
    calc
      p = 3 • p - 2 • p := by abel
      _ = 0 := by rw [hp3, hp2, sub_zero]
  have hs : ({0,p,-p} : Finset G).card = Fintype.card G := by
    rw [Fintype.card_eq_nat_card, hcard]
    simp [hpn, hp.symm, (neg_ne_zero.mpr hp).symm]
  have hq : q ∈ ({0,p,-p} : Finset G) := by rw [Finset.eq_univ_of_card _ hs]; simp
  simpa using hq

section Generic

variable {K L G : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [AddCommGroup G] [Finite G] [DistribMulAction (L ≃ₐ[K] L) G]

/-- Ratios of coordinates with the same nonzero inversion parity descend to the base field. -/
lemma ratio_fixed (hcard : Nat.card G = 3) (p : G) (hp : p ≠ 0)
    (ε : L) (hε : ε ≠ 0)
    (f g : G →[L ≃ₐ[K] L] L)
    (hfn : f (-p) = ε * f p) (hgn : g (-p) = ε * g p) :
    ∃ c : K, algebraMap K L c = g p / f p := by
  apply (InfiniteGalois.mem_range_algebraMap_iff_fixed _).mpr
  intro σ
  have hs (v : G →[L ≃ₐ[K] L] L) : σ (v p) = v (σ • p) := by
    simpa only [AlgEquiv.smul_def] using (map_smul v σ p).symm
  rw [map_div₀, hs g, hs f]
  rcases three_cases hcard p hp (σ • p) with h | h | h
  · exact False.elim (hp (by simpa using congrArg (σ⁻¹ • ·) h))
  · rw [h]
  · rw [h, hfn, hgn, mul_div_mul_left _ _ hε]

/-- Equivariant augmentation functions with the same nonzero inversion parity are proportional. -/
lemma proportional (hcard : Nat.card G = 3) (ε : L) (hε : ε ≠ 0)
    (f g : G →[L ≃ₐ[K] L] L) (hf : f ≠ 0)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hfn : ∀ p, f (-p) = ε * f p) (hgn : ∀ p, g (-p) = ε * g p) :
    ∃ c : K, g = c • f := by
  classical
  obtain ⟨p, hp⟩ : ∃ p, f p ≠ 0 := by
    by_contra h
    apply hf
    ext p
    simpa using (not_exists.mp h p)
  have hp0 : p ≠ 0 := fun h ↦ hp (h ▸ hf0)
  obtain ⟨c,hc⟩ := ratio_fixed hcard p hp0 ε hε f g (hfn p) (hgn p)
  have hcp : g p = algebraMap K L c * f p := by rw [hc, div_mul_cancel₀ _ hp]
  refine ⟨c, ?_⟩
  ext q
  change g q = (MulActionHom.evalAlgHom (L ≃ₐ[K] L) K G L q) (c • f)
  rw [map_smul, Algebra.smul_def]
  change g q = (algebraMap K L) c * f q
  rcases three_cases hcard p hp0 q with rfl | rfl | rfl
  · simp [hf0,hg0]
  · simpa [Algebra.smul_def] using hcp
  · simp [hfn, hgn, hcp, mul_left_comm]

/-- Equivariant augmentation functions on which inversion acts by a specified scalar. -/
def paritySubmodule (ε : L) : Submodule K (G →[L ≃ₐ[K] L] L) where
  carrier := {f | f 0 = 0 ∧ ∀ p, f (-p) = ε * f p}
  zero_mem' := by constructor <;> simp
  add_mem' := by
    intro f g hf hg
    constructor
    · change (MulActionHom.evalAlgHom (L ≃ₐ[K] L) K G L 0) (f + g) = 0
      rw [map_add]
      change f 0 + g 0 = 0
      rw [hf.1, hg.1, add_zero]
    · intro p
      change (MulActionHom.evalAlgHom (L ≃ₐ[K] L) K G L (-p)) (f + g) =
        ε * (MulActionHom.evalAlgHom (L ≃ₐ[K] L) K G L p) (f + g)
      rw [map_add, map_add]
      change f (-p) + g (-p) = ε * (f p + g p)
      rw [hf.2 p, hg.2 p, mul_add]
  smul_mem' c f hf := by
    constructor
    · change (MulActionHom.evalAlgHom (L ≃ₐ[K] L) K G L 0) (c • f) = 0
      rw [map_smul]
      change c • f 0 = 0
      rw [hf.1, smul_zero]
    · intro p
      change (MulActionHom.evalAlgHom (L ≃ₐ[K] L) K G L (-p)) (c • f) =
        ε * (MulActionHom.evalAlgHom (L ≃ₐ[K] L) K G L p) (c • f)
      rw [map_smul, map_smul]
      change c • f (-p) = ε * (c • f p)
      rw [hf.2 p, Algebra.smul_def, Algebra.smul_def]
      ring

/-- Each nonzero inversion eigenspace in the augmentation functions has rank at most one. -/
lemma parity_rank_le_one (hcard : Nat.card G = 3) (ε : L) (hε : ε ≠ 0) :
    Module.rank K (paritySubmodule (K := K) (G := G) ε) ≤ 1 := by
  classical
  let M := paritySubmodule (K := K) (G := G) ε
  apply rank_le_one_iff.mpr
  by_cases h : ∀ f : M, f = 0
  · exact ⟨0, fun g ↦ ⟨0, by simp [h g]⟩⟩
  push Not at h
  obtain ⟨f, hf⟩ := h
  refine ⟨f, fun g ↦ ?_⟩
  have hf' : (f : G →[L ≃ₐ[K] L] L) ≠ 0 := fun h ↦ hf (Subtype.ext h)
  obtain ⟨c,hc⟩ := proportional hcard ε hε (f : G →[L ≃ₐ[K] L] L)
    (g : G →[L ≃ₐ[K] L] L) hf' f.property.1 g.property.1
    f.property.2 g.property.2
  exact ⟨c, Subtype.ext hc.symm⟩
end Generic

/-- The algebraic closure of the three-adic fraction field. -/
abbrev Ω := AlgebraicClosure ℚ_[3]

/-- Scalar restriction on equivariant coordinates agrees with the fraction-field tower. -/
instance coordsTower (X : FF ℤ_[3] ℚ_[3]) :
    IsScalarTower ℤ_[3] ℚ_[3] (X.Points →[Ω ≃ₐ[ℚ_[3]] Ω] Ω) := by
  apply IsScalarTower.of_algebraMap_eq
  intro r
  ext p
  change algebraMap ℤ_[3] Ω r = algebraMap ℚ_[3] Ω (algebraMap ℤ_[3] ℚ_[3] r)
  exact IsScalarTower.algebraMap_apply ℤ_[3] ℚ_[3] Ω r

/-- Integral coordinates viewed as equivariant functions on the geometric generic points. -/
noncomputable def coords (X : FF ℤ_[3] ℚ_[3]) :
    X.CoordinateRing →ₐ[ℤ_[3]] (X.Points →[Ω ≃ₐ[ℚ_[3]] Ω] Ω) :=
  (X.genericCoordinates.symm.toAlgEquiv.toAlgHom.restrictScalars ℤ_[3]).comp
    Algebra.TensorProduct.includeRight

/-- An integral coordinate is determined by its geometric generic values. -/
lemma coords_injective (X : FF ℤ_[3] ℚ_[3]) : Function.Injective (coords X) :=
  X.genericCoordinates.symm.injective.comp
    (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective ℤ_[3] ℚ_[3]))

/-- The integral antipode acts on geometric coordinates by negating the point. -/
lemma coords_antipode (X : FF ℤ_[3] ℚ_[3]) (a : X.CoordinateRing) (p : X.Points) :
    coords X (HopfAlgebra.antipode ℤ_[3] a) p = coords X a (-p) := by
  let := GaloisModule.GenericFiber.hopfAlgebra ℚ_[3] Ω X.Points
  have h := LinearMap.congr_fun (BialgHom.antipode_comp X.genericCoordinates.symm.toBialgHom)
    (1 ⊗ₜ[ℤ_[3]] a)
  have ht : HopfAlgebra.antipode ℚ_[3] (1 ⊗ₜ[ℤ_[3]] a) =
      (1 : ℚ_[3]) ⊗ₜ[ℤ_[3]] (HopfAlgebra.antipode ℤ_[3] a) := by simp
  change HopfAlgebra.antipode ℚ_[3] (X.genericCoordinates.symm (1 ⊗ₜ[ℤ_[3]] a)) =
    X.genericCoordinates.symm (HopfAlgebra.antipode ℚ_[3] (1 ⊗ₜ[ℤ_[3]] a)) at h
  rw [ht] at h
  have h' := congrArg (fun f : X.Points →[Ω ≃ₐ[ℚ_[3]] Ω] Ω ↦ f p) h
  exact h'.symm

/-- The integral counit is evaluation at the identity point. -/
lemma coords_counit (X : FF ℤ_[3] ℚ_[3]) (a : X.CoordinateRing) :
    coords X a 0 = algebraMap ℤ_[3] Ω (Coalgebra.counit (R := ℤ_[3]) a) := by
  let := GaloisModule.GenericFiber.hopfAlgebra ℚ_[3] Ω X.Points
  have h := CoalgHomClass.counit_comp_apply X.genericCoordinates.symm.toBialgHom
    (1 ⊗ₜ[ℤ_[3]] a)
  have h' := congrArg (algebraMap ℚ_[3] Ω) h
  change algebraMap ℚ_[3] Ω (GaloisModule.GenericFiber.counitAlgHom ℚ_[3] Ω X.Points
    (coords X a)) = _ at h'
  rw [GaloisModule.GenericFiber.algebraMap_counitAlgHom] at h'
  simpa only [TensorProduct.counit_tmul, map_one, Bialgebra.counit_one, one_mul, mul_one,
    Algebra.smul_def, ← IsScalarTower.algebraMap_apply ℤ_[3] ℚ_[3] Ω] using h'

/-- The integral augmentation submodule with specified inversion eigenvalue. -/
noncomputable def integralParity (X : FF ℤ_[3] ℚ_[3]) (ε : ℤ_[3]) :
    Submodule ℤ_[3] X.CoordinateRing :=
  (HopfAlgebra.antipode ℤ_[3] (A := X.CoordinateRing) - ε • LinearMap.id).ker ⊓
    (Coalgebra.counit (R := ℤ_[3])).ker

/-- Membership in an integral inversion eigenspace. -/
lemma mem_integralParity (X : FF ℤ_[3] ℚ_[3]) (ε : ℤ_[3]) (a : X.CoordinateRing) :
    a ∈ integralParity X ε ↔ HopfAlgebra.antipode ℤ_[3] a = ε • a ∧
      Coalgebra.counit (R := ℤ_[3]) a = 0 := by
  simp [integralParity, sub_eq_zero]

/-- Integral augmentation eigenspaces have rank at most one for order-three models. -/
lemma integralParity_rank (X : FF ℤ_[3] ℚ_[3]) (hcard : Nat.card X.Points = 3)
    (ε : ℤ_[3]) (hε : ε ≠ 0) : Module.rank ℤ_[3] (integralParity X ε) ≤ 1 := by
  let P := paritySubmodule (K := ℚ_[3]) (G := X.Points) (algebraMap ℤ_[3] Ω ε)
  let j : integralParity X ε →ₗ[ℤ_[3]] P :=
    ((coords X).toLinearMap.comp (integralParity X ε).subtype).codRestrict
      (P.restrictScalars ℤ_[3]) (by
        intro a
        obtain ⟨ha,hc⟩ := (mem_integralParity X ε a).mp a.property
        constructor
        · change coords X a 0 = 0
          rw [coords_counit, hc, map_zero]
        · intro p
          change coords X a (-p) = algebraMap ℤ_[3] Ω ε * coords X a p
          rw [← coords_antipode, ha, map_smul]
          change (MulActionHom.evalAlgHom (Ω ≃ₐ[ℚ_[3]] Ω) ℤ_[3] X.Points Ω p)
            (ε • coords X a) = _
          rw [map_smul, Algebra.smul_def]
          rfl)
  have hj : Function.Injective j := by
    intro a b h
    apply Subtype.ext
    apply coords_injective X
    exact congrArg Subtype.val h
  calc
    Module.rank ℤ_[3] (integralParity X ε) ≤ Module.rank ℤ_[3] P := j.rank_le_of_injective hj
    _ = Module.rank ℚ_[3] P := (IsFractionRing.rank_right_eq ℤ_[3] ℚ_[3] P).symm
    _ ≤ 1 := parity_rank_le_one hcard _ (by
      rw [IsScalarTower.algebraMap_apply ℤ_[3] ℚ_[3] Ω]
      simpa only [map_zero] using (FaithfulSMul.algebraMap_injective ℚ_[3] Ω).ne
        ((IsFractionRing.injective ℤ_[3] ℚ_[3]).ne hε))

/-- The antipode on a finite flat model with commutative generic points is involutive. -/
lemma antipode_involutive (X : FF ℤ_[3] ℚ_[3]) (a : X.CoordinateRing) :
    HopfAlgebra.antipode ℤ_[3] (HopfAlgebra.antipode ℤ_[3] a) = a := by
  apply coords_injective X
  ext p
  simp only [coords_antipode, neg_neg]

/-- Two is invertible in the three-adic integers. -/
lemma half_exists : ∃ t : ℤ_[3], 2*t=1 := by
  apply isUnit_iff_exists_inv.mp
  rw [PadicInt.isUnit_iff]
  exact PadicInt.norm_natCast_eq_one_iff.mpr (by decide : Nat.Coprime 3 2)

/-- The integral module rank equals the number of geometric generic points. -/
lemma model_finrank (X : FF ℤ_[3] ℚ_[3]) :
    Module.finrank ℤ_[3] X.CoordinateRing = Nat.card X.Points := by
  let : Module.Free ℤ_[3] X.CoordinateRing := Module.free_of_flat_of_isLocalRing
  rw [← Module.finrank_baseChange (R := ℚ_[3])]
  exact (X.genericCoordinates.toAlgEquiv.toLinearEquiv.finrank_eq).symm.trans
    (GaloisModule.finrank_equivariantFunctions ℚ_[3] Ω X.Points)

/-- Sum the scalar, odd augmentation, and even augmentation coordinates. -/
noncomputable def inversionMerge (X : FF ℤ_[3] ℚ_[3]) :
    (ℤ_[3] × integralParity X (-1) × integralParity X 1) →ₗ[ℤ_[3]] X.CoordinateRing where
  toFun a := algebraMap ℤ_[3] X.CoordinateRing a.1 + a.2.1 + a.2.2
  map_add' a b := by simp; abel
  map_smul' r a := by simp [Algebra.smul_def]; ring

/-- Splitting by the two inversion projectors decomposes the integral coordinate module. -/
lemma inversion_merge_bijective (X : FF ℤ_[3] ℚ_[3]) :
    Function.Bijective (inversionMerge X) := by
  obtain ⟨t, ht⟩ := half_exists
  have hhalf (a : X.CoordinateRing) : t • (a + a) = a := by
    rw [← two_smul ℤ_[3], smul_smul, mul_comm t 2, ht, one_smul]
  have hhalfR (a : ℤ_[3]) : t * (a+a) = a := by linear_combination a*ht
  let S := HopfAlgebra.antipode ℤ_[3] (A := X.CoordinateRing)
  let C := Coalgebra.counit (R := ℤ_[3]) (A := X.CoordinateRing)
  let U := Algebra.linearMap ℤ_[3] X.CoordinateRing
  let o : X.CoordinateRing →ₗ[ℤ_[3]] integralParity X (-1) :=
    (t • (LinearMap.id - S)).codRestrict _ (by
      intro a
      rw [mem_integralParity]
      change S (t • (a - S a)) = (-1 : ℤ_[3]) • (t • (a - S a)) ∧ _
      constructor
      · simp only [map_smul, map_sub, S, antipode_involutive, neg_one_smul]
        module
      · change C (t • (a - S a)) = 0
        simp [C,S])
  let e : X.CoordinateRing →ₗ[ℤ_[3]] integralParity X 1 :=
    (t • (LinearMap.id + S) - U.comp C).codRestrict _ (by
      intro a
      rw [mem_integralParity]
      change S (t • (a + S a) - U (C a)) = (1 : ℤ_[3]) • _ ∧ _
      constructor
      · simp [S, U, antipode_involutive, add_comm, Algebra.algebraMap_eq_smul_one]
      · change C (t • (a + S a) - U (C a)) = 0
        simp [C,S,U, hhalfR, Algebra.smul_def])
  let j := C.prod (o.prod e)
  have hj (a : X.CoordinateRing) : U (j a).1 + (j a).2.1 + (j a).2.2 = a := by
    change U (C a) + t • (a - S a) + (t • (a + S a) - U (C a)) = a
    calc
      _ = t • (a+a) := by module
      _ = a := hhalf a
  have hleft : ∀ a, j (inversionMerge X a) = a := by
    rintro ⟨r, x, z⟩
    obtain ⟨hx,hxc⟩ := (mem_integralParity X (-1) x).mp x.property
    obtain ⟨hz,hzc⟩ := (mem_integralParity X 1 z).mp z.property
    simp only [neg_one_smul] at hx
    simp only [one_smul] at hz
    have hc : C (U r + x + z) = r := by simp [C,U,hxc,hzc]
    have hs : S (U r + x + z) = U r - x + z := by
      simp [S, U, hx, hz, sub_eq_add_neg, Algebra.algebraMap_eq_smul_one]
    apply Prod.ext
    · exact hc
    · apply Prod.ext <;> apply Subtype.ext
      · change t • (U r + x + z - S (U r + x + z)) = x
        rw [hs]
        convert hhalf x using 2; module
      · change t • (U r + x + z + S (U r + x + z)) -
          U (C (U r + x + z)) = z
        rw [hs,hc]
        calc
          _ = t • ((U r + z) + (U r + z)) - U r := by module
          _ = z := by rw [hhalf]; abel
  exact ⟨fun a b h ↦ (hleft a).symm.trans ((congrArg j h).trans (hleft b)),
    fun a ↦ ⟨j a, hj a⟩⟩

/-- For an order-three model, both augmentation eigenspaces have rank exactly one. -/
lemma inversion_parity_finrank (X : FF ℤ_[3] ℚ_[3]) (hcard : Nat.card X.Points = 3) :
    Module.finrank ℤ_[3] (integralParity X (-1)) = 1 ∧
      Module.finrank ℤ_[3] (integralParity X 1) = 1 := by
  let : Module.Free ℤ_[3] X.CoordinateRing := Module.free_of_flat_of_isLocalRing
  have h := (LinearEquiv.ofBijective (inversionMerge X) (inversion_merge_bijective X)).finrank_eq
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_self, model_finrank, hcard] at h
  have ho : Module.finrank ℤ_[3] (integralParity X (-1)) ≤ 1 :=
    Module.finrank_le_of_rank_le (by simpa using integralParity_rank X hcard (-1) (by norm_num))
  have he : Module.finrank ℤ_[3] (integralParity X 1) ≤ 1 :=
    Module.finrank_le_of_rank_le (by simpa using integralParity_rank X hcard 1 one_ne_zero)
  omega

/-- Every order-three three-adic model has a basis adapted to inversion and augmentation. -/
lemma inversion_basis (X : FF ℤ_[3] ℚ_[3]) (hcard : Nat.card X.Points = 3) :
    ∃ (x z : X.CoordinateRing) (b : Module.Basis (Fin 3) ℤ_[3] X.CoordinateRing),
      b 0 = 1 ∧ b 1 = x ∧ b 2 = z ∧ HopfAlgebra.antipode ℤ_[3] x = -x ∧
        HopfAlgebra.antipode ℤ_[3] z = z ∧ Coalgebra.counit (R := ℤ_[3]) z = 0 := by
  classical
  let : Module.Free ℤ_[3] X.CoordinateRing := Module.free_of_flat_of_isLocalRing
  obtain ⟨ho, he⟩ := inversion_parity_finrank X hcard
  let bo := Module.basisUnique (Fin 1) ho
  let be := Module.basisUnique (Fin 1) he
  let ix : Fin 3 ≃ Fin 1 ⊕ (Fin 1 ⊕ Fin 1) :=
    { toFun := ![Sum.inl 0, Sum.inr (Sum.inl 0), Sum.inr (Sum.inr 0)]
      invFun := Sum.elim (fun _ ↦ 0) (Sum.elim (fun _ ↦ 1) (fun _ ↦ 2))
      left_inv := by intro i; fin_cases i <;> rfl
      right_inv := by rintro (i | (i | i)) <;> fin_cases i <;> rfl }
  let b := (((Module.Basis.singleton (Fin 1) ℤ_[3]).prod (bo.prod be)).map
    (LinearEquiv.ofBijective (inversionMerge X) (inversion_merge_bijective X))).reindex ix.symm
  refine ⟨bo 0, be 0, b, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [b, Module.Basis.prod_apply, ix, inversionMerge]
  · simp [b, Module.Basis.prod_apply, ix, inversionMerge]
  · simp [b, Module.Basis.prod_apply, ix, inversionMerge]
  · simpa only [neg_one_smul] using ((mem_integralParity X (-1) _).mp (bo 0).property).1
  · simpa only [one_smul] using ((mem_integralParity X 1 _).mp (be 0).property).1
  · exact ((mem_integralParity X 1 _).mp (be 0).property).2

/-- A finite flat model with reduced generic fibre is reduced. -/
lemma model_reduced (X : FF ℤ_[3] ℚ_[3]) : IsReduced X.CoordinateRing := by
  constructor
  intro a ha
  apply coords_injective X
  ext p
  rw [map_zero]
  exact (ha.map ((MulActionHom.evalAlgHom (Ω ≃ₐ[ℚ_[3]] Ω) ℤ_[3] X.Points Ω p).comp
    (coords X))).eq_zero

/-- Every order-three three-adic model admits an Oort–Tate power presentation. -/
lemma model_presentation (X : FF ℤ_[3] ℚ_[3]) (hcard : Nat.card X.Points = 3) :
    Nonempty (OortTateThreeBasis ℤ_[3] X.CoordinateRing) := by
  let : Coalgebra.IsCocomm ℤ_[3] X.CoordinateRing :=
    cocomm_of_injective_points X.points.toAddMonoidHom X.points_bijective.1
  let : IsReduced X.CoordinateRing := model_reduced X
  obtain ⟨x,z,b,h0,h1,h2,hx,hz,hc⟩ := inversion_basis X hcard
  exact nonempty_oortTateThreeBasis_of_inversion_basis x z b h0 h1 h2 hx hz hc

end ThreeAdicPlan.RankThree
