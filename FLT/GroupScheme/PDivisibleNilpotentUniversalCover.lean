/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleUniversalCover
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-! # Formal etaleness of original inverse-p sequences for nilpotent thickenings -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)
  {B C D : Type} [CommRing B] [CommRing C] [CommRing D]
  [Algebra R B] [Algebra R C] [Algebra R D]

/-- Identity coefficients act identically on inverse-p sequences. -/
theorem universalCoverMap_id (x : X.UniversalCover B) :
    X.universalCoverMap (AlgHom.id R B) x = x := by
  apply Subtype.ext
  funext n
  exact X.pointColimitMap_id (x.val n)

/-- Coefficient equivalences induce actual equivalences of compatible sequences. -/
def universalCoverEquiv (e : B ≃ₐ[R] C) : X.UniversalCover B ≃ X.UniversalCover C where
  toFun := X.universalCoverMap e.toAlgHom
  invFun := X.universalCoverMap e.symm.toAlgHom
  left_inv x := by rw [← X.universalCoverMap_comp, AlgEquiv.symm_comp, X.universalCoverMap_id]
  right_inv x := by rw [← X.universalCoverMap_comp, AlgEquiv.comp_symm, X.universalCoverMap_id]

/-- Bijectivity is preserved under the specified coefficient-map composition. -/
theorem universalCoverMap_bijective_comp (q : B →ₐ[R] C) (q' : C →ₐ[R] D)
    (hq : Function.Bijective (X.universalCoverMap q))
    (hq' : Function.Bijective (X.universalCoverMap q')) :
    Function.Bijective (X.universalCoverMap (q'.comp q)) := by
  have he : X.universalCoverMap (q'.comp q) = X.universalCoverMap q' ∘ X.universalCoverMap q :=
    funext (X.universalCoverMap_comp q q')
  rw [he]
  exact hq'.comp hq

/-- Induction through powers of a nilpotent ideal preserves unique compatible lifting. -/
theorem universalCoverMap_bijective_nilpotent_quotient (I : Ideal B)
    (hI : IsNilpotent I) (hB : IsNilpotent (p : B)) :
    Function.Bijective (X.universalCoverMap (Ideal.Quotient.mkₐ R I)) := by
  revert hB
  revert ‹Algebra R B›
  apply Ideal.IsNilpotent.induction_on I hI
  · intro B _ I hI _ hB
    obtain ⟨s, hs⟩ := hB
    apply (X.universalCoverSquareZeroEquiv (Ideal.Quotient.mkₐ R I)
      Ideal.Quotient.mk_surjective _ s _).bijective
    · change RingHom.ker (Ideal.Quotient.mk I) ^ 2 = ⊥
      simpa only [Ideal.mk_ker] using hI
    · intro b _
      rw [nsmul_eq_mul, Nat.cast_pow, hs, zero_mul]
  · intro B _ I J hIJ h₁ h₂ _ hB
    let e : ((B ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)) ≃ₐ[R] B ⧸ J :=
      { (DoubleQuot.quotQuotEquivQuotSup I J).trans
          (Ideal.quotEquivOfEq (sup_eq_right.mpr hIJ)) with commutes' := fun _ ↦ rfl }
    have hBI : IsNilpotent (p : B ⧸ I) := by
      simpa only [map_natCast] using hB.map (Ideal.Quotient.mk I)
    have he : e.toAlgHom.comp ((Ideal.Quotient.mkₐ R _).comp (Ideal.Quotient.mkₐ R I)) =
        Ideal.Quotient.mkₐ R J := by ext b; rfl
    have hb := X.universalCoverMap_bijective_comp _ e.toAlgHom
      (X.universalCoverMap_bijective_comp _ _ (h₁ hB) (h₂ hBI))
      (X.universalCoverEquiv e).bijective
    rwa [he] at hb

/-- Nilpotent surjections of p-nilpotent test rings uniquely lift inverse-p sequences. -/
theorem universalCoverMap_bijective_nilpotent (q : B →ₐ[R] C) (hq : Function.Surjective q)
    (hJ : IsNilpotent (RingHom.ker q)) (hB : IsNilpotent (p : B)) :
    Function.Bijective (X.universalCoverMap q) := by
  let e := Ideal.quotientKerAlgEquivOfSurjective hq
  have he : e.toAlgHom.comp (Ideal.Quotient.mkₐ R (RingHom.ker q)) = q := by ext b; rfl
  have hb := X.universalCoverMap_bijective_comp _ e.toAlgHom
    (X.universalCoverMap_bijective_nilpotent_quotient _ hJ hB) (X.universalCoverEquiv e).bijective
  rwa [he] at hb

end ThreeAdicPlan.PDivisibleSystem
