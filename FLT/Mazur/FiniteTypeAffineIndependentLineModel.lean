/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypeBaseIndependentLineModel

/-!
# Noetherian models on actual affine test schemes

Transport through the affine scheme's canonical spectrum isomorphism gives
a model for every line on an actual affine test. The test square and its
original structural map are retained, without any choice of ring coordinates.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.Approximation
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X Y S : Scheme.{0}} [IsAffine S] {a : X ⟶ Y} {f : X ⟶ S}
  {q : Y ⟶ Spec (.of R)} {g : S ⟶ Spec (.of R)}
  [IsProper q] [Flat q] [GeometricallyIntegral q] (h : IsPullback a f q g)

include h in
/-- Every affine test line has an actual proper flat integral Noetherian model. -/
theorem finiteTypeAffine_independent_line_model (L : X.Modules) (hL : LocallyFreeRankOne L) :
    ∃ (Z B : Scheme.{0}) (r : Z ⟶ B) (p : X ⟶ Z) (b : S ⟶ B) (M : Z.Modules),
      IsLocallyNoetherian B ∧ IsProper r ∧ Flat r ∧ GeometricallyIntegral r ∧
        LocallyFreeRankOne M ∧ IsPullback p f r b ∧ Nonempty ((pullback p).obj M ≅ L) := by
  have H₀ : IsPullback (𝟙 X) (f ≫ S.isoSpec.hom) f S.isoSpec.inv :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have H : IsPullback a (f ≫ S.isoSpec.hom) q (S.isoSpec.inv ≫ g) := by
    simpa only [Category.id_comp] using H₀.paste_horiz h
  let k := Spec.preimage (S.isoSpec.inv ≫ g)
  have Hk : IsPullback a (f ≫ S.isoSpec.hom) q (Spec.map k) := by
    simpa only [k, Spec.map_preimage] using H
  obtain ⟨Z, B, r, p, b, M, hB, hr, hflat, hint, hM, H', he⟩ :=
    finiteTypeBase_independent_line_model k.hom Hk L hL
  have H₁ : IsPullback (𝟙 X) f (f ≫ S.isoSpec.hom) S.isoSpec.hom :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  refine ⟨Z, B, r, p, S.isoSpec.hom ≫ b, M, hB, hr, hflat, hint, hM, ?_, he⟩
  simpa only [Category.id_comp] using H₁.paste_horiz H'

end FLT.Mazur.Approximation
