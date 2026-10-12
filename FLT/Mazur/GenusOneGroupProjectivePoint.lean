/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GenusOneGroupProjectiveIso
public import FLT.Mazur.WeierstrassNonzeroPointAffine

/-!
# The original specified point maps to infinity

The constructed isomorphism identifies the whole point complement with the
whole affine cubic. Its missing point is consequently the actual zero section.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GenusOneGroupCoordinates
open FCurve WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {k : Type} [Field k] [IsAlgClosed k]
  (G : Over (Spec (.of k))) [GrpObj G] [IsIntegral G.left] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom]
  (hd : topologicalKrullDim G.left = 1) (hc : HasConstantGlobalSections G.hom)
  (hg : curveGenus G.hom hd hc = 1)
  (s : 𝟙_ (Over (Spec (.of k))) ⟶ G) (hI : EffectiveCartier s.left.ker)

/-- The original specified point cannot map into the affine cubic chart. -/
theorem toProjective_point_not_affine (x : Spec (.of k)) :
    toProjective G hd hc hg s hI (s.left x) ∉
      Set.range (integralCurveChart (equation G hd hc hg s hI) 2) := by
  let W := equation G hd hc hg s hI
  let U := complement G s
  let f := toProjective G hd hc hg s hI
  let e := affineIso G hd hc hg s hI
  let _ : IsIso f := toProjective_isIso G hd hc hg s hI
  have hc : (monicChartIso W).inv ≫ e.inv ≫ U.ι ≫ f = integralCurveChart W 2 := by
    rw [toProjective_restrict]
    change _ ≫ _ ≫ (e.hom ≫ (monicChartIso W).hom ≫ integralCurveChart W 2) = _
    simp only [Iso.inv_hom_id_assoc]
  rintro ⟨z, hz⟩
  let v := e.inv ((monicChartIso W).inv z)
  have hv : U.ι v = s.left x := by
    apply f.isOpenEmbedding.injective
    exact (congrArg (fun t ↦ t z) hc).trans hz
  have hm := v.2
  change U.ι v ∈ U at hm
  rw [hv] at hm
  change _ ∉ (s.left.ker.support : Set G.left) at hm
  rw [support_section_ker G.hom s.left s.w] at hm
  exact hm ⟨x, rfl⟩

/-- The complete coordinate isomorphism takes the original point to the infinity section. -/
theorem toProjective_point : s.left ≫ toProjective G hd hc hg s hI =
    integralCurveZero (equation G hd hc hg s hI) := by
  classical
  let W := equation G hd hc hg s hI
  let _ : W.IsElliptic := equation_isElliptic G hd hc hg s hI
  let hΔ := WeierstrassCurve.isUnit_Δ W
  let P : integralGroupFieldPoints (K := k) W hΔ :=
    Over.homMk (s.left ≫ toProjective G hd hc hg s hI) (by
      change _ ≫ integralCurveStructure W = _
      rw [Category.assoc, toProjective_over, s.w]
      simp)
  have hP : P = 1 := by
    by_contra hP
    obtain ⟨t, ht⟩ := nonzeroPoint_factor W hΔ P hP
    let x : Spec (.of k) := ⟨⊥, inferInstance⟩
    exact toProjective_point_not_affine G hd hc hg s hI x
      ⟨t x, congrArg (fun z ↦ z x) ht⟩
  have he := congrArg (fun z : integralGroupFieldPoints (K := k) W hΔ ↦ z.left) hP
  change s.left ≫ toProjective G hd hc hg s hI =
    Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫ integralCurveZero W at he
  simpa using he

end FLT.Mazur.GenusOneGroupCoordinates
