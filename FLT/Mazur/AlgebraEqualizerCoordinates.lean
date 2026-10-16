/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatAlgebraEqualizerNaturality

/-!
# Full equalizers under changes of coefficient coordinates

Compatible algebra equivalences on the source and relation identify the entire
endpoint equalizers. This retains the source inclusion, so lifting certificates
can subsequently be transported without losing their coefficient ring.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.AlgebraEqualizerCoordinates
variable {R A D A' D' : Type*}
  [CommRing R] [CommRing A] [CommRing D] [CommRing A'] [CommRing D']
  [Algebra R A] [Algebra R D] [Algebra R A'] [Algebra R D']
  (p q : A →ₐ[R] D) (p' q' : A' →ₐ[R] D')
  (a : A ≃ₐ[R] A') (d : D ≃ₐ[R] D')
  (hp : p'.comp a.toAlgHom = d.toAlgHom.comp p)
  (hq : q'.comp a.toAlgHom = d.toAlgHom.comp q)

include hp hq in
/-- The original two equations hold exactly when their coordinate images hold. -/
theorem mem_iff (x : A) : a x ∈ AlgHom.equalizer p' q' ↔ x ∈ AlgHom.equalizer p q := by
  change p' (a x) = q' (a x) ↔ p x = q x
  have hp' : p' (a x) = d (p x) := DFunLike.congr_fun hp x
  have hq' : q' (a x) = d (q x) := DFunLike.congr_fun hq x
  rw [hp', hq']
  exact d.injective.eq_iff

/-- The full equalizer equivalence is induced by the original source equivalence. -/
def equiv : AlgHom.equalizer p q ≃ₐ[R] AlgHom.equalizer p' q' :=
  AlgEquiv.ofBijective
    (FlatAlgebraEqualizer.equalizerMap p q p' q' a.toAlgHom d.toAlgHom hp hq) (by
      constructor
      · intro x y h
        apply Subtype.ext
        exact a.injective (congrArg Subtype.val h)
      · intro x
        refine ⟨⟨a.symm x.val, ?_⟩, ?_⟩
        · apply (mem_iff p q p' q' a d hp hq _).mp
          simpa only [a.apply_symm_apply] using x.property
        · exact Subtype.ext (a.apply_symm_apply x.val))

/-- The comparison keeps the actual inclusion in the source function ring. -/
theorem equiv_val (x : AlgHom.equalizer p q) :
    (equiv p q p' q' a d hp hq x).val = a x.val := rfl

/-- The inverse also retains the actual source coefficient. -/
theorem equiv_symm_val (x : AlgHom.equalizer p' q') :
    ((equiv p q p' q' a d hp hq).symm x).val = a.symm x.val := by
  apply a.injective
  rw [a.apply_symm_apply]
  exact congrArg Subtype.val ((equiv p q p' q' a d hp hq).apply_symm_apply x)

end FLT.Mazur.AlgebraEqualizerCoordinates
