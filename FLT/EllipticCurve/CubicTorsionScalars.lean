/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicNonzeroTorsion
/-! # Changing the generator of a represented torsion point -/

open AlgebraicGeometry CategoryTheory MonoidalCategory MonObj
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
  (W : WeierstrassCurve R) [W.IsElliptic]
/-- Inverse residue classes give inverse multiplication morphisms on the torsion scheme. -/
theorem torsionScalar_composite (n : ℕ) (a b : ℕ)
    (h : a * b ≡ 1 [MOD n]) :
    ((𝟙 (torsionModel W n)) ^ a) ≫ ((𝟙 (torsionModel W n)) ^ b) = 𝟙 _ := by
  rw [MonObj.comp_pow, Category.comp_id, ← pow_mul]
  exact (pow_eq_pow_of_modEq h (torsionPoint_pow_eq_one W n (𝟙 _))).trans (pow_one _)

/-- A unit modulo n acts by a genuine automorphism of the torsion scheme. -/
def torsionScalarIso (n : ℕ) [NeZero n] (a : (ZMod n)ˣ) :
    torsionModel W n ≅ torsionModel W n where
  hom := (𝟙 (torsionModel W n)) ^ a.val.val
  inv := (𝟙 (torsionModel W n)) ^ (a⁻¹).val.val
  hom_inv_id := torsionScalar_composite W n _ _ (by
    apply (ZMod.natCast_eq_natCast_iff _ _ n).mp
    simp)
  inv_hom_id := torsionScalar_composite W n _ _ (by
    apply (ZMod.natCast_eq_natCast_iff _ _ n).mp
    simp)

/-- Scalar automorphisms preserve the zero section. -/
theorem torsionScalarIso_zero (n : ℕ) [NeZero n] (a : (ZMod n)ˣ) :
    torsionZeroSection W n ≫ (torsionScalarIso W n a).hom.left = torsionZeroSection W n := by
  have h : η[torsionModel W n] ≫ (torsionScalarIso W n a).hom =
      η[torsionModel W n] := by
    change η[torsionModel W n] ≫ (𝟙 (torsionModel W n)) ^ a.val.val = _
    rw [MonObj.comp_pow, Category.comp_id, MonObj.one_eq_one, one_pow]
  exact congrArg Over.Hom.left h

/-- The inverse scalar automorphism preserves the zero section. -/
theorem torsionScalarIso_inv_zero (n : ℕ) [NeZero n] (a : (ZMod n)ˣ) :
    torsionZeroSection W n ≫ (torsionScalarIso W n a).inv.left = torsionZeroSection W n := by
  exact torsionScalarIso_zero W n a⁻¹

/-- Scalar automorphisms preserve the nonzero torsion locus. -/
theorem torsionScalarIso_mem_nonzero (n : ℕ) [NeZero n] (a : (ZMod n)ˣ)
    (x : (torsionModel W n).left) (hx : x ∈ nonzeroTorsionOpen W n) :
    (torsionScalarIso W n a).hom.left x ∈ nonzeroTorsionOpen W n := by
  intro hy
  obtain ⟨y, hy⟩ := hy
  apply hx
  refine ⟨y, ?_⟩
  have h := congrArg (fun z => (torsionScalarIso W n a).inv.left z) hy
  have hz := congrArg (fun f : Spec (.of R) ⟶ (torsionModel W n).left => f y)
    (torsionScalarIso_inv_zero W n a)
  have hi := congrArg (fun f : torsionModel W n ⟶ torsionModel W n => f.left x)
    (torsionScalarIso W n a).hom_inv_id
  exact hz.symm.trans (h.trans hi)

instance nonzeroTorsionInclusionMono (n : ℕ) [NeZero n] :
    Mono (nonzeroTorsionInclusion W n) := by
  have : Mono (nonzeroTorsionInclusion W n).left :=
    inferInstanceAs (Mono (nonzeroTorsionOpen W n).ι)
  exact Over.mono_of_mono_left _

/-- A scalar unit changes the generator in the nonzero torsion parameter scheme. -/
def nonzeroTorsionScalarHom (n : ℕ) [NeZero n] (a : (ZMod n)ˣ) :
    nonzeroTorsionModel W n ⟶ nonzeroTorsionModel W n :=
  (nonzeroTorsionPointEquiv W n (nonzeroTorsionModel W n)).symm
    ⟨nonzeroTorsionInclusion W n ≫ (torsionScalarIso W n a).hom, by
      rintro _ ⟨x, rfl⟩
      exact torsionScalarIso_mem_nonzero W n a x.val x.property⟩

/-- The restricted scalar map agrees with multiplication on the full torsion scheme. -/
theorem nonzeroTorsionScalarHom_inclusion (n : ℕ) [NeZero n] (a : (ZMod n)ˣ) :
    nonzeroTorsionScalarHom W n a ≫ nonzeroTorsionInclusion W n =
      nonzeroTorsionInclusion W n ≫ (torsionScalarIso W n a).hom :=
  congrArg Subtype.val ((nonzeroTorsionPointEquiv W n (nonzeroTorsionModel W n)).apply_symm_apply _)

/-- Changing the generator by a scalar unit is an isomorphism of parameter schemes. -/
def nonzeroTorsionScalarIso (n : ℕ) [NeZero n] (a : (ZMod n)ˣ) :
    nonzeroTorsionModel W n ≅ nonzeroTorsionModel W n where
  hom := nonzeroTorsionScalarHom W n a
  inv := nonzeroTorsionScalarHom W n a⁻¹
  hom_inv_id := by
    apply (cancel_mono (nonzeroTorsionInclusion W n)).mp
    rw [Category.assoc, nonzeroTorsionScalarHom_inclusion, ← Category.assoc,
      nonzeroTorsionScalarHom_inclusion, Category.assoc]
    have h : (torsionScalarIso W n a).hom ≫ (torsionScalarIso W n a⁻¹).hom = 𝟙 _ :=
      (torsionScalarIso W n a).hom_inv_id
    rw [h, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (nonzeroTorsionInclusion W n)).mp
    rw [Category.assoc, nonzeroTorsionScalarHom_inclusion, ← Category.assoc,
      nonzeroTorsionScalarHom_inclusion, Category.assoc]
    have h : (torsionScalarIso W n a⁻¹).hom ≫ (torsionScalarIso W n a).hom = 𝟙 _ :=
      (torsionScalarIso W n a).inv_hom_id
    rw [h, Category.comp_id, Category.id_comp]

/-- The identity scalar acts as the identity scheme morphism. -/
theorem torsionScalarIso_one (n : ℕ) [NeZero n] :
    (torsionScalarIso W n 1).hom = 𝟙 _ := by
  change (𝟙 (torsionModel W n)) ^ (1 : ZMod n).val = _
  have h : (1 : ZMod n).val ≡ 1 [MOD n] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ n).mp
    simp
  exact (pow_eq_pow_of_modEq h (torsionPoint_pow_eq_one W n (𝟙 _))).trans (pow_one _)

/-- Scalar multiplication respects composition of scheme automorphisms. -/
theorem torsionScalarIso_mul (n : ℕ) [NeZero n] (a b : (ZMod n)ˣ) :
    (torsionScalarIso W n (a * b)).hom =
      (torsionScalarIso W n b).hom ≫ (torsionScalarIso W n a).hom := by
  change (𝟙 (torsionModel W n)) ^ (a * b).val.val =
    ((𝟙 (torsionModel W n)) ^ b.val.val) ≫ ((𝟙 (torsionModel W n)) ^ a.val.val)
  rw [MonObj.comp_pow, Category.comp_id, ← pow_mul]
  apply pow_eq_pow_of_modEq _ (torsionPoint_pow_eq_one W n (𝟙 _))
  apply (ZMod.natCast_eq_natCast_iff _ _ n).mp
  simp [mul_comm]

/-- The units modulo n act on the actual nonzero torsion scheme. -/
def nonzeroTorsionScalarAction (n : ℕ) [NeZero n] :
    (ZMod n)ˣ →* Aut (nonzeroTorsionModel W n) where
  toFun := nonzeroTorsionScalarIso W n
  map_one' := by
    apply Iso.ext
    apply (cancel_mono (nonzeroTorsionInclusion W n)).mp
    change nonzeroTorsionScalarHom W n 1 ≫ nonzeroTorsionInclusion W n = _
    rw [nonzeroTorsionScalarHom_inclusion, torsionScalarIso_one]
    exact (Category.id_comp _).symm
  map_mul' a b := by
    apply Iso.ext
    apply (cancel_mono (nonzeroTorsionInclusion W n)).mp
    change nonzeroTorsionScalarHom W n (a * b) ≫ nonzeroTorsionInclusion W n =
      (nonzeroTorsionScalarHom W n b ≫ nonzeroTorsionScalarHom W n a) ≫
        nonzeroTorsionInclusion W n
    rw [nonzeroTorsionScalarHom_inclusion, Category.assoc,
      nonzeroTorsionScalarHom_inclusion, ← Category.assoc,
      nonzeroTorsionScalarHom_inclusion, Category.assoc, torsionScalarIso_mul]


/-- The scheme scalar automorphism is ordinary scalar multiplication on classical torsion. -/
theorem torsionScalarIso_classical (n : ℕ) [NeZero n] (a : (ZMod n)ˣ)
    (K : Type u) [Field K] [Algebra R K] [DecidableEq K]
    (p : pointSource (R := R) K ⟶ torsionModel W n) :
    (classicalTorsionMulEquiv W K n (p ≫ (torsionScalarIso W n a).hom)).toAdd.val =
      a.val.val • (classicalTorsionMulEquiv W K n p).toAdd.val := by
  change (classicalTorsionMulEquiv W K n
    (p ≫ (𝟙 (torsionModel W n)) ^ a.val.val)).toAdd.val = _
  rw [MonObj.comp_pow, Category.comp_id, map_pow]
  rfl

/-- The generator change agrees with scalar multiplication under the nonzero-point comparison. -/
theorem nonzeroTorsionScalarIso_classical (n : ℕ) [NeZero n]
    (hn : IsUnit (n : R)) (a : (ZMod n)ˣ)
    (K : Type u) [Field K] [Algebra R K] [DecidableEq K]
    (p : pointSource (R := R) K ⟶ nonzeroTorsionModel W n) :
    (nonzeroTorsionClassicalEquiv W n hn K
      (p ≫ (nonzeroTorsionScalarIso W n a).hom)).val.val =
      a.val.val • (nonzeroTorsionClassicalEquiv W n hn K p).val.val := by
  change (classicalTorsionMulEquiv W K n
    ((p ≫ nonzeroTorsionScalarHom W n a) ≫ nonzeroTorsionInclusion W n)).toAdd.val = _
  rw [Category.assoc, nonzeroTorsionScalarHom_inclusion, ← Category.assoc,
    torsionScalarIso_classical]
  rfl

/-- At prime level the scalar action is free on all field-valued nonzero torsion points. -/
theorem nonzeroTorsionScalar_field_free (p : ℕ) [Fact p.Prime] [NeZero p]
    (hp : IsUnit (p : R)) (a : (ZMod p)ˣ)
    (K : Type u) [Field K] [Algebra R K]
    (q : pointSource (R := R) K ⟶ nonzeroTorsionModel W p)
    (h : q ≫ (nonzeroTorsionScalarIso W p a).hom = q) : a = 1 := by
  classical
  let P := (nonzeroTorsionClassicalEquiv W p hp K q).val
  have hP : addOrderOf P.val = p :=
    addOrderOf_eq_prime P.property
      (fun h => (nonzeroTorsionClassicalEquiv W p hp K q).property (Subtype.ext h))
  have he := congrArg (fun t => (nonzeroTorsionClassicalEquiv W p hp K t).val.val) h
  rw [nonzeroTorsionScalarIso_classical] at he
  have hm : a.val.val ≡ 1 [MOD p] := by
    have hm' : a.val.val ≡ 1 [MOD addOrderOf P.val] :=
      nsmul_eq_nsmul_iff_modEq.mp (by simpa only [one_nsmul] using he)
    simpa only [hP] using hm'
  apply Units.ext
  simpa using (ZMod.natCast_eq_natCast_iff _ _ p).mpr hm

end WeierstrassCurve.CubicCharts
