/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CurveEndomorphismDichotomy
public import FLT.Mazur.GroupObjectPointTranslation

/-!
# Fixed-point-free automorphisms of proper group curves are translations

Subtract the normalized automorphism from the identity. The resulting curve
morphism is either constant or surjective. The first case makes normalization
trivial; the second supplies a fixed point of the original automorphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
namespace FLT.Mazur.GroupObjectPointTranslation
open FCurve
set_option backward.isDefEq.respectTransparency false
universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
  {G : Over (Spec (.of K))} [GrpObj G] [IsIntegral G.left] [IsProper G.hom]
  (hd : topologicalKrullDim G.left ≤ 1) (e : G ≅ G)

include hd in
/-- A fixed-point-free automorphism of a proper integral group curve is its point translation. -/
theorem fixedPointFree_eq_translation
    (hf : ∀ q : 𝟙_ (Over (Spec (.of K))) ⟶ G, q ≫ e.hom ≠ q) :
    e.hom = translation ((1 : 𝟙_ (Over (Spec (.of K))) ⟶ G) ≫ e.hom) := by
  apply (eq_translation_iff e).mpr
  let g := (normalizedIso e).hom
  let d : G ⟶ G := 𝟙 G / g
  let o : 𝟙_ (Over (Spec (.of K))) ⟶ G := 1
  have hod : o ≫ d = 1 := by
    dsimp only [d, o, g]
    rw [GrpObj.comp_div, Category.comp_id, normalizedIso_one]
    exact one_div_one
  obtain hs | hc := curveEndomorphism_surjective_or_constant G.hom hd o.left o.w d.left d.w
  · let p : 𝟙_ (Over (Spec (.of K))) ⟶ G := o ≫ e.hom
    obtain ⟨q, hq, hqd⟩ := curveEndomorphism_rationalPoint_lift G.hom d.left d.w
      hs p.left p.w
    let q' : 𝟙_ (Over (Spec (.of K))) ⟶ G := Over.homMk q hq
    have hq'd : q' ≫ d = p := by
      apply Over.OverMorphism.ext
      exact hqd
    have hdq : q' / (q' ≫ g) = p := by
      simpa only [d, GrpObj.comp_div, Category.comp_id] using hq'd
    have hr : q' ≫ e.hom = p * (q' ≫ g) := by
      rw [← normalizedIso_translation e, ← Category.assoc, comp_translation]
      simp only [toUnit_unit, Category.id_comp]
      rfl
    exact ((hf q') (hr.trans (hdq.symm ▸ div_mul_cancel q' (q' ≫ g)))).elim
  · have hd : d = 1 := by
      apply Over.OverMorphism.ext
      calc
        d.left = G.hom ≫ (o ≫ d).left := hc
        _ = (1 : G ⟶ G).left := by
          rw [hod]
          rfl
    exact (div_eq_one.mp hd).symm

end FLT.Mazur.GroupObjectPointTranslation
