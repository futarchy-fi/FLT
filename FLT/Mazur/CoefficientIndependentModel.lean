/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientCommonModel

/-!
# Comparison of models over independently chosen coefficient rings

Both coefficient rings embed in one finite stage. Common-model comparison
then supplies a single whole-family model recovering both original choices.
The construction retains any prescribed finite set of original coefficients.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.Approximation
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Models over unrelated finite coefficient rings have a common Cartesian refinement. -/
theorem exists_independent_coefficient_common_model {A : Type u} [CommRing A]
    (R S : Subalgebra ℤ A) [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ S]
    {X Y Z : Scheme.{u}} {r : X ⟶ Spec (.of A)}
    (p : Y ⟶ Spec (.of R)) (q : Z ⟶ Spec (.of S))
    [QuasiCompact p] [QuasiCompact q]
    [LocallyOfFinitePresentation p] [LocallyOfFinitePresentation q]
    {a : X ⟶ Y} {b : X ⟶ Z}
    (hp : IsPullback a r p (Spec.map (CommRingCat.ofHom R.val.toRingHom)))
    (hq : IsPullback b r q (Spec.map (CommRingCat.ofHom S.val.toRingHom)))
    (c₀ : Set A) (hc₀ : c₀.Finite) :
    ∃ (T : Subalgebra ℤ A) (_ : Algebra.FiniteType ℤ T) (_ : c₀ ⊆ T)
      (hRT : R ≤ T) (hST : S ≤ T)
      (W : Scheme.{u}) (v : W ⟶ Spec (.of T)) (u : X ⟶ W)
      (c : W ⟶ Y) (d : W ⟶ Z),
      IsPullback c v p (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRT).toRingHom)) ∧
      IsPullback d v q (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hST).toRingHom)) ∧
      IsPullback u r v (Spec.map (CommRingCat.ofHom T.val.toRingHom)) ∧
      u ≫ c = a ∧ u ≫ d = b := by
  obtain ⟨B, hB, hcB, hRB, hSB⟩ := exists_common_coefficient_extension R
    (fun _ : Unit ↦ S) (fun _ ↦ inferInstance) c₀ hc₀
  let i : (CoefficientStage R)ᵒᵖ := .op ⟨B, hRB, hB⟩
  let j : (CoefficientStage S)ᵒᵖ := .op ⟨B, hSB (), hB⟩
  let br := (coefficientSpectrumToInitial R).app i
  let bs := (coefficientSpectrumToInitial S).app j
  obtain ⟨T, hT, hBT, W, v, u, c, d, hcp, hdq, huv, huc, hud⟩ :=
    exists_coefficient_common_model B (pullback.snd p br) (pullback.snd q bs)
      (coefficientModelRecovery_isPullback hp i) (coefficientModelRecovery_isPullback hq j)
  have hbr : Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hBT).toRingHom) ≫ br =
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (hRB.trans hBT)).toRingHom) := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  have hbs : Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hBT).toRingHom) ≫ bs =
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion ((hSB ()).trans hBT)).toRingHom) := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  have hc := hcp.paste_horiz (IsPullback.of_hasPullback p br)
  have hd := hdq.paste_horiz (IsPullback.of_hasPullback q bs)
  rw [hbr] at hc
  rw [hbs] at hd
  refine ⟨T, hT, fun x hx ↦ hBT (hcB hx), hRB.trans hBT, (hSB ()).trans hBT,
    W, v, u, c ≫ pullback.fst p br, d ≫ pullback.fst q bs, hc, hd, huv, ?_, ?_⟩
  · rw [← Category.assoc, huc, coefficientModelRecovery_fst]
  · rw [← Category.assoc, hud, coefficientModelRecovery_fst]

end FLT.Mazur.Approximation
