/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.FiniteFieldQuadraticSpectrum
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Prime-field characteristic polynomials of actual rank-one scalar actions

Transport the operator to multiplication on its derived scalar field.
Cayley–Hamilton supplies its scalar root; Frobenius supplies the quadratic partner.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace LinearMap
open Polynomial

variable {p : ℕ} [Fact p.Prime] {F W k : Type*} [Field F] [CharP F p]
  [Finite F] [AddCommGroup W] [Module (ZMod p) W] [Module F W]
  [Module.Finite (ZMod p) W] [Field k] [CharP k p]
  (T : Module.End (ZMod p) W) (hdim : Module.finrank F W = 1)
  (a : F) (ha : ∀ w, T w = a • w) (ε : F →+* k)

include hdim ha

omit [CharP k p] in
/-- The scalar of the original operator is a root of its prime-field charpoly. -/
theorem isRoot_charpoly_of_rank_one_scalar :
    (T.charpoly.map (ε.comp (ZMod.castHom (dvd_refl p) F))).IsRoot (ε a) := by
  let : Algebra (ZMod p) F := (ZMod.castHom (dvd_refl p) F).toAlgebra
  let eF : W ≃ₗ[F] F := (Module.nonempty_linearEquiv_of_finrank_eq_one hdim).some.symm
  let e : W ≃ₗ[ZMod p] F := eF.restrictScalars (ZMod p)
  have he : e.conj T = Algebra.lmul (ZMod p) F a := by
    ext x
    change eF (T (eF.symm x)) = a * x
    rw [ha, eF.map_smul, eF.apply_symm_apply, smul_eq_mul]
  have hroot : (T.charpoly.map (algebraMap (ZMod p) F)).IsRoot a := by
    have h := Algebra.aeval_self_charpoly_lmul (R := ZMod p) a
    rw [← he, e.charpoly_conj T] at h
    simpa only [IsRoot, eval_map, aeval_def] using h
  change (T.charpoly.map (ε.comp (algebraMap (ZMod p) F))).IsRoot (ε a)
  simpa only [map_map] using hroot.map (f := ε)

omit [CharP k p] in
/-- A one-dimensional prime-field factor has the scalar linear charpoly. -/
theorem charpoly_rank_one_scalar (hW : Module.finrank (ZMod p) W = 1) :
    T.charpoly.map (ε.comp (ZMod.castHom (dvd_refl p) F)) = X - C (ε a) := by
  apply eq_of_monic_of_dvd_of_natDegree_le (monic_X_sub_C _) (T.charpoly_monic.map _)
  · exact dvd_iff_isRoot.mpr (T.isRoot_charpoly_of_rank_one_scalar hdim a ha ε)
  · rw [natDegree_map_eq_of_injective (RingHom.injective _) T.charpoly,
      T.charpoly_natDegree, hW, natDegree_X_sub_C]

/-- A distinct Frobenius orbit gives the two prime-field factor eigenvalues. -/
theorem charpoly_rank_two_scalar (hW : Module.finrank (ZMod p) W = 2)
    (hne : ε a ≠ (ε a) ^ p) :
    T.charpoly.map (ε.comp (ZMod.castHom (dvd_refl p) F)) =
      (X - C (ε a)) * (X - C ((ε a) ^ p)) :=
  map_eq_frobenius_factors _ _ T.charpoly_monic (T.charpoly_natDegree.trans hW)
    (T.isRoot_charpoly_of_rank_one_scalar hdim a ha ε) hne


/-- The quadratic formula also holds when the scalar is fixed by Frobenius. -/
theorem charpoly_rank_two_scalar_factors (hW : Module.finrank (ZMod p) W = 2) :
    T.charpoly.map (ε.comp (ZMod.castHom (dvd_refl p) F)) =
      (X - C (ε a)) * (X - C ((ε a) ^ p)) := by
  by_cases hne : ε a ≠ (ε a) ^ p
  · exact T.charpoly_rank_two_scalar hdim a ha ε hW hne
  have hfix : (ε a) ^ p = ε a := (not_ne_iff.mp hne).symm
  have haF : a ^ p = a := ε.injective (by simpa only [map_pow] using hfix)
  obtain ⟨n, hn⟩ := (mem_bot_iff_intCast p F).mp
    ((Subfield.mem_bot_iff_pow_eq_self F p).mpr haF)
  have hT : T = (n : ZMod p) • LinearMap.id := by
    ext w
    simpa only [← hn, Int.cast_smul_eq_zsmul, LinearMap.smul_apply,
      LinearMap.id_apply] using ha w
  have hpoly : T.charpoly = (X - C (n : ZMod p)) ^ 2 := by
    let b := Module.Free.chooseBasis (ZMod p) W
    rw [← charpoly_toMatrix T b, hT, map_smul, toMatrix_id,
      Matrix.smul_one_eq_diagonal, Matrix.charpoly_diagonal]
    simp only [Finset.prod_const, Finset.card_univ, ← Module.finrank_eq_card_chooseBasisIndex,
      hW]
  rw [hpoly, Polynomial.map_pow, Polynomial.map_sub, map_X, map_C, hfix]
  simp only [map_intCast, ← hn, pow_two]

end LinearMap
