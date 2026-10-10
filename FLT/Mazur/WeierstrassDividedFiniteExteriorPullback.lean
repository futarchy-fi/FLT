/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedExteriorProper
public import FLT.Mazur.WeierstrassDividedFiniteIteration

/-!
# Full unchanged exterior pullbacks through finite iteration

Reassociation preserves the complete exterior pullback, not only its
commutative square. Pasting these squares identifies the entire inverse
image of the initial exterior at every finite stage.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0)

/-- The complete old exterior is unchanged under the already constructed whole step. -/
theorem Exterior.step_exterior_isPullback {k : ℕ} {d : Data W π k} (E : Exterior d)
    (e : Data W π (k + 1)) :
    IsPullback (𝟙 E.carrier) (E.retained hπ e ≫ (E.advance hπ e).exteriorChart)
      E.exteriorChart (E.stepContraction hπ e) := by
  apply (E.localReplacement_exterior_isPullback hπ e).of_iso
    (Iso.refl _) (Iso.refl _) (E.advanceIso hπ e).symm (Iso.refl _)
  · simp
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.id_comp]
    rw [Iso.comp_inv_eq]
    simpa only [Category.assoc, localBoundary] using (E.advanceIso_retained hπ e).symm
  · simp
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
    rw [← E.advanceIso_contraction hπ e, Iso.inv_hom_id_assoc]

variable {start n : ℕ} (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (E : Exterior (data ⟨0, Nat.zero_lt_succ n⟩))

/-- Every finite composite has the identity over the full original exterior. -/
theorem finiteExterior_isPullback (j : ℕ) (hj : j ≤ n) :
    IsPullback (𝟙 E.carrier)
      (finiteRetained hπ data E j hj ≫ (finiteExterior hπ data E j hj).exteriorChart)
      E.exteriorChart (finiteContraction hπ data E j hj) := by
  induction j with
  | zero =>
    simpa [finiteRetained, finiteExterior, finiteContraction, finiteWhole] using
      (IsPullback.of_id_fst (f := E.exteriorChart))
  | succ j ih =>
    have hstep := (IsPullback.of_id_fst
      (f := finiteRetained hπ data E j (Nat.le_of_succ_le hj))).paste_vert
        ((finiteExterior hπ data E j (Nat.le_of_succ_le hj)).step_exterior_isPullback
          hπ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩))
    have h := hstep.paste_horiz (ih (Nat.le_of_succ_le hj))
    simpa only [finiteRetained, finiteExterior, finiteContraction, finiteStep,
      Category.id_comp, Category.assoc] using h

/-- No extra points occur over the retained original exterior after any finite iteration. -/
theorem finiteExterior_preimage (j : ℕ) (hj : j ≤ n) :
    finiteContraction hπ data E j hj ⁻¹' Set.range E.exteriorChart =
      Set.range (finiteRetained hπ data E j hj ≫
        (finiteExterior hπ data E j hj).exteriorChart) := by
  have h := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
    (finiteExterior_isPullback hπ data E j hj) ⊤
  simpa [Set.range_comp, finiteWhole] using (congrArg SetLike.coe h).symm

end FLT.Mazur.WeierstrassDividedDepth
