/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypeRelativeLineModel

/-!
# Relative line models on original affine tests

An independent line on an actual affine test has an affine parameter model
of finite presentation over the unchanged fixed base. Both original maps
and cartesian squares survive the change from ring coordinates.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.Approximation
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X Y S : Scheme} [IsAffine S] {a : X ⟶ Y} {f : X ⟶ S}
  {q : Y ⟶ Spec (.of R)} {g : S ⟶ Spec (.of R)}
  [IsProper q] (H : IsPullback a f q g)

include H in
/-- Actual affine-test lines have finitely presented parameter models over the original base. -/
theorem exists_affine_relative_line_model (L : X.Modules) (hL : LocallyFreeRankOne L) :
    ∃ (Z B : Scheme) (r : Z ⟶ B) (t : Z ⟶ Y) (p : X ⟶ Z)
      (b : S ⟶ B) (u : B ⟶ Spec (.of R)) (M : Z.Modules),
      IsAffine B ∧ IsLocallyNoetherian B ∧ LocallyOfFinitePresentation u ∧
        IsPullback t r q u ∧ IsPullback p f r b ∧ p ≫ t = a ∧ b ≫ u = g ∧
        LocallyFreeRankOne M ∧ Nonempty ((Scheme.Modules.pullback p).obj M ≅ L) := by
  have H₀ : IsPullback (𝟙 X) (f ≫ S.isoSpec.hom) f S.isoSpec.inv :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have H' : IsPullback a (f ≫ S.isoSpec.hom) q (S.isoSpec.inv ≫ g) := by
    simpa only [Category.id_comp] using H₀.paste_horiz H
  let k := Spec.preimage (S.isoSpec.inv ≫ g)
  have Hk : IsPullback a (f ≫ S.isoSpec.hom) q (Spec.map k) := by
    simpa only [k, Spec.map_preimage] using H'
  obtain ⟨Z, B, r, t, p, b, u, M, hB, hN, hu, HB, Hp, ht, hb, hM, he⟩ :=
    exists_finiteType_relative_line_model k.hom Hk L hL
  have H₁ : IsPullback (𝟙 X) f (f ≫ S.isoSpec.hom) S.isoSpec.hom :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  refine ⟨Z, B, r, t, p, S.isoSpec.hom ≫ b, u, M, hB, hN, hu, HB, ?_, ht, ?_, hM, he⟩
  · simpa only [Category.id_comp] using H₁.paste_horiz Hp
  · rw [Category.assoc, hb]
    change S.isoSpec.hom ≫ Spec.map k = g
    simp only [k, Spec.map_preimage, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end FLT.Mazur.Approximation
