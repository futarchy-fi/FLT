/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGlobalModificationRegularLiftExt
public import FLT.Mazur.WeierstrassGlobalModificationUnchangedLift
public import FLT.Mazur.WeierstrassGlobalModificationFractionCover

/-!
# The contraction detects maps compared to a flat reference map

An arbitrary competitor of a flat map to the entire modification is determined
by its contraction. The proof pulls back the original fraction/infinity cover;
flatness retains the regular original denominator on every affine refinement.
This supplies cancellation for identity and inverse action laws without
asserting that the contraction is a monomorphism.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassGlobalModification

open WeierstrassIntegralChart WeierstrassModificationReesCoordinates
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R B : Type u} [CommRing R] [IsDomain R] [IsBezout R] [CommRing B]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) (hs : s ≠ 0)

/-- Flat affine maps to original fraction inputs have no alternative contracted lift. -/
theorem originalFraction_flat_lift_ext (i : Option (Fin 3))
    (p : Spec (.of B) ⟶ Spec (originalFractionCoverRing W s i)) [Flat p]
    (f : Spec (.of B) ⟶ model W s b3 b4 b6 h3 h4 h6 hs)
    (hf : f ≫ contraction W s b3 b4 b6 h3 h4 h6 hs =
      p ≫ originalFractionCoverMap W s b3 b4 b6 h3 h4 h6 hs i ≫
        contraction W s b3 b4 b6 h3 h4 h6 hs) :
    f = p ≫ originalFractionCoverMap W s b3 b4 b6 h3 h4 h6 hs i := by
  cases i with
  | none =>
    apply lift_eq_infinity
    rw [hf, originalFractionCoverMap_none_contraction]
  | some i =>
    let I := modificationChartCenter W s 2
    let a := centerGenerators W s i
    let ψ := affineChartRingHom p
    let φ := ψ.comp (algebraMap (Coordinate W 2) (BlowupFractionChart.chart I a))
    have hp : Spec.map (CommRingCat.ofHom ψ) = p := affineChartRingHom_spec p
    have hflat : ψ.Flat := by
      apply (Flat.SpecMap_iff (f := CommRingCat.ofHom ψ)).mp
      rw [hp]
      infer_instance
    have hI : I.map φ = Ideal.span {ψ (BlowupFractionChart.denominator I a)} :=
      BlowupFractionChart.center_map_eq_mapped_denominator I a (centerGenerators_mem W s i) ψ
    have hd : IsRegular (ψ (BlowupFractionChart.denominator I a)) :=
      flatRingHom_isRegular ψ hflat (BlowupFractionChart.denominator_regular I a)
    have hc : (p ≫ originalFractionCoverMap W s b3 b4 b6 h3 h4 h6 hs (some i)) ≫
        contraction W s b3 b4 b6 h3 h4 h6 hs =
          Spec.map (CommRingCat.ofHom φ) ≫ integralCurveChart W 2 := by
      rw [Category.assoc, originalFractionCoverMap_some_contraction]
      change p ≫ Spec.map (CommRingCat.ofHom (algebraMap (Coordinate W 2)
        (BlowupFractionChart.chart I a))) ≫ integralCurveChart W 2 = _
      rw [show φ = ψ.comp (algebraMap _ _) from rfl,
        CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hp]
    apply regular_center_lift_ext W s b3 b4 b6 h3 h4 h6 hs φ _ hI hd f
      (p ≫ originalFractionCoverMap W s b3 b4 b6 h3 h4 h6 hs (some i))
    · exact hf.trans ((Category.assoc _ _ _).symm.trans hc)
    · exact hc

/-- Contraction detects any competitor of a flat map into the entire modification. -/
theorem contraction_ext_of_flat {T : Scheme.{u}}
    (p : T ⟶ model W s b3 b4 b6 h3 h4 h6 hs) [Flat p]
    (f : T ⟶ model W s b3 b4 b6 h3 h4 h6 hs)
    (hf : f ≫ contraction W s b3 b4 b6 h3 h4 h6 hs =
      p ≫ contraction W s b3 b4 b6 h3 h4 h6 hs) : f = p := by
  let C := (originalFractionCover W s b3 b4 b6 h3 h4 h6 hs).openCover
  let D := C.pullback₁ p
  apply Scheme.Cover.hom_ext D
  intro i
  apply (D.X i).affineCover.hom_ext
  intro k
  let q := (D.X i).affineCover.f k ≫ C.pullbackHom p i
  have hq : Flat q := by dsimp [q, Scheme.Cover.pullbackHom]; infer_instance
  have he : q ≫ C.f i = (D.X i).affineCover.f k ≫ D.f i ≫ p := by
    dsimp only [q]
    rw [Category.assoc, Scheme.Cover.pullbackHom_map]
  have hh := originalFraction_flat_lift_ext W s b3 b4 b6 h3 h4 h6 hs i q
    ((D.X i).affineCover.f k ≫ D.f i ≫ f) (by
      change _ = q ≫ C.f i ≫ contraction W s b3 b4 b6 h3 h4 h6 hs
      rw [← Category.assoc q, he]
      simp only [Category.assoc, hf])
  exact hh.trans he

end FLT.Mazur.WeierstrassGlobalModification
