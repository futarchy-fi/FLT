/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.AbsoluteGaloisGroup.RootCharacterResidue
public import FLT.AbsoluteGaloisGroup.FundamentalTame
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Finite coefficients for fundamental characters

Niveau r means coefficients in the field of p^r elements, for the prime p.
Embeddings of this finite field differ by a power of Frobenius.
-/

@[expose] public section

open Polynomial IsLocalRing NumberField
namespace LocalRoot

section FiniteFields
variable (k : Type*) [Field k] (p r : ℕ) [Fact p.Prime] [CharP k p]

/-- The subfield fixed by the r-th power of the p-Frobenius. -/
def levelField : Subfield k := (iterateFrobenius k p r).eqLocusField (RingHom.id k)

/-- Membership is the defining finite-field equation. -/
@[simp] theorem mem_levelField (x : k) : x ∈ levelField k p r ↔ x ^ (p ^ r) = x := Iff.rfl

/-- The level field consists precisely of the roots of X^(p^r)-X. -/
theorem levelField_eq_rootSet (hr : 0 < r) :
    (levelField k p r : Set k) = (X ^ p ^ r - X : k[X]).rootSet k := by
  ext x
  change x ∈ levelField k p r ↔ _
  rw [mem_levelField, mem_rootSet_of_ne
    (FiniteField.X_pow_card_pow_sub_X_ne_zero k hr.ne' (Fact.out : p.Prime).one_lt)]
  simp [sub_eq_zero]

/-- Positive levels have finitely many elements. -/
theorem levelField_finite (hr : 0 < r) : Finite (levelField k p r) := by
  rw [← SetLike.coe_sort_coe, levelField_eq_rootSet k p r hr]
  infer_instance

/-- In an algebraically closed field the level field has exactly p^r elements. -/
theorem levelField_card [IsAlgClosed k] (hr : 0 < r) :
    Nat.card (levelField k p r) = p ^ r := by
  rw [← SetLike.coe_sort_coe, levelField_eq_rootSet k p r hr, Nat.card_eq_fintype_card,
    card_rootSet_eq_natDegree (galois_poly_separable p _ (dvd_pow_self p hr.ne'))
      (IsAlgClosed.splits _)]
  exact FiniteField.X_pow_card_pow_sub_X_natDegree_eq k hr.ne' (Fact.out : p.Prime).one_lt

/-- Embed just the finite coefficient field in the algebraic closure of Fp. -/
noncomputable def levelEmbedding (hr : 0 < r) :
    levelField k p r →+* AlgebraicClosure (ZMod p) := by
  let := levelField_finite k p r hr
  let := ZMod.algebra (levelField k p r) p
  exact (IsAlgClosed.lift (R := ZMod p) (S := levelField k p r)
    (M := AlgebraicClosure (ZMod p))).toRingHom

variable {k p r}

/-- Every coefficient embedding lands in the same finite subfield of the target. -/
noncomputable def levelEmbeddingRestriction
    (ι : levelField k p r →+* AlgebraicClosure (ZMod p)) :
    levelField k p r →+* levelField (AlgebraicClosure (ZMod p)) p r :=
  ι.codRestrict _ fun x ↦ by
    change (ι x) ^ (p ^ r) = ι x
    rw [← map_pow]
    exact congrArg ι (Subtype.ext x.2)

/-- Each embedding identifies the source and target finite subfields. -/
theorem levelEmbeddingRestriction_bijective [IsAlgClosed k] (hr : 0 < r)
    (ι : levelField k p r →+* AlgebraicClosure (ZMod p)) :
    Function.Bijective (levelEmbeddingRestriction ι) := by
  let := levelField_finite (AlgebraicClosure (ZMod p)) p r hr
  apply (levelEmbeddingRestriction ι).injective.bijective_of_nat_card_le
  rw [levelField_card k p r hr, levelField_card (AlgebraicClosure (ZMod p)) p r hr]

/-- Embeddings of the finite coefficient field differ by a bounded Frobenius power. -/
theorem levelEmbedding_frobenius [IsAlgClosed k] (hr : 0 < r)
    (ι j : levelField k p r →+* AlgebraicClosure (ZMod p)) :
    ∃ i < r, ∀ x, j x = (ι x) ^ (p ^ i) := by
  let F := levelField k p r
  let := levelField_finite k p r hr
  let := ZMod.algebra F p
  let eι := RingEquiv.ofBijective (levelEmbeddingRestriction ι)
    (levelEmbeddingRestriction_bijective hr ι)
  let ej := RingEquiv.ofBijective (levelEmbeddingRestriction j)
    (levelEmbeddingRestriction_bijective hr j)
  let e : F ≃ₐ[ZMod p] F :=
    { __ := ej.trans eι.symm
      commutes' x := RingHom.congr_fun (Subsingleton.elim
        ((ej.trans eι.symm).toRingHom.comp (algebraMap (ZMod p) F))
        (algebraMap (ZMod p) F)) x }
  have hd : Module.finrank (ZMod p) F = r := by
    apply Nat.pow_right_injective (Fact.out : p.Prime).one_lt
    change p ^ Module.finrank (ZMod p) F = p ^ r
    rw [FiniteField.pow_finrank_eq_natCard, levelField_card k p r hr]
  obtain ⟨i, hi⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) F).2 e
  refine ⟨i.1, hd ▸ i.2, fun x ↦ ?_⟩
  have he : e x = x ^ (p ^ i.1) := by
    rw [← hi]
    simp [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic, pow_iterate]
  have hx := congrArg (fun y : F ↦ (eι y : AlgebraicClosure (ZMod p))) he
  simpa [e, eι, ej, levelEmbeddingRestriction, map_pow] using hx

variable (k p r)

/-- Prime-to-p roots of unity give units in the corresponding level field. -/
noncomputable def rootsToLevelUnits :
    rootsOfUnity (p ^ r - 1) k →* (levelField k p r)ˣ where
  toFun u := Units.mk0 ⟨(u.1 : k), by
    change (u.1 : k) ^ (p ^ r) = (u.1 : k)
    have hu : (u.1 : k) ^ (p ^ r - 1) = 1 :=
      congrArg Units.val ((mem_rootsOfUnity _ _).mp u.2)
    calc
      (u.1 : k) ^ (p ^ r) = (u.1 : k) ^ (p ^ r - 1 + 1) := by
        rw [Nat.sub_add_cancel (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos)]
      _ = (u.1 : k) := by rw [pow_succ, hu, one_mul]⟩
    (fun h ↦ Units.ne_zero u.1 (congrArg Subtype.val h))
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

end FiniteFields

variable {K : Type*} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
local notation "Kv" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "k" => ResidueField (IntegralClosure O (AlgebraicClosure Kv))

variable (p r : ℕ) [Fact p.Prime]
  [CharP (ResidueField (IntegralClosure (v.adicCompletionIntegers K)
    (AlgebraicClosure (v.adicCompletion K)))) p]

/-- The root-ratio character with its finite field of coefficients. -/
noncomputable def levelCharacter (hr : 0 < r) {π : O}
    (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ))
    {α : AlgebraicClosure Kv}
    (hα : α ^ (p ^ r - 1) = algebraMap Kv (AlgebraicClosure Kv) π.1) :
    localInertiaGroup v →* (levelField k p r)ˣ :=
  (rootsToLevelUnits k p r).comp
    (rootCharacterToRoots v (Nat.sub_pos_of_lt
      (Nat.one_lt_pow hr.ne' (Fact.out : p.Prime).one_lt)) hπ hα)

/-- A fundamental character with a chosen embedding of the finite coefficient field. -/
noncomputable def fundamentalCharacter (hr : 0 < r) {π : O}
    (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ))
    {α : AlgebraicClosure Kv}
    (hα : α ^ (p ^ r - 1) = algebraMap Kv (AlgebraicClosure Kv) π.1)
    (ι : levelField k p r →+* AlgebraicClosure (ZMod p)) :
    localInertiaGroup v →* (AlgebraicClosure (ZMod p))ˣ :=
  (Units.map ι.toMonoidHom).comp (levelCharacter v p r hr hπ hα)

/-- Changing the coefficient embedding applies a power of p-Frobenius. -/
theorem fundamentalCharacter_frobenius (hr : 0 < r) {π : O}
    (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ))
    {α : AlgebraicClosure Kv}
    (hα : α ^ (p ^ r - 1) = algebraMap Kv (AlgebraicClosure Kv) π.1)
    (ι j : levelField k p r →+* AlgebraicClosure (ZMod p)) :
    ∃ i < r, ∀ σ : localInertiaGroup v,
      fundamentalCharacter v p r hr hπ hα j σ =
        fundamentalCharacter v p r hr hπ hα ι σ ^ (p ^ i) := by
  let := residue_isAlgClosed v
  obtain ⟨i, hi, he⟩ := levelEmbedding_frobenius hr ι j
  refine ⟨i, hi, fun σ ↦ Units.ext ?_⟩
  exact he (levelCharacter v p r hr hπ hα σ)

end LocalRoot
