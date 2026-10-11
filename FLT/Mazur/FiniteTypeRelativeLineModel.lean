/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypeBaseIndependentLineModel

/-!
# Finite-type translation-line models over the original fixed base

An independent line on an arbitrary ring test descends to a finite-type
affine parameter base over the original base, with finite presentation. Both original geometric maps
and both cartesian squares are retained, together with the full line isomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.Approximation
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R A : Type} [CommRing R] [CommRing A] [Algebra.FiniteType ℤ R]
  {X Y : Scheme} {a : X ⟶ Y} {f : X ⟶ Spec (.of A)} {q : Y ⟶ Spec (.of R)}
  [IsProper q]
  (g : R →+* A) (H : IsPullback a f q (Spec.map (CommRingCat.ofHom g)))

include H in
/-- An actual translation line has a finite-type model retaining its original relative geometry. -/
theorem exists_finiteType_relative_line_model (L : X.Modules) (hL : LocallyFreeRankOne L) :
    ∃ (Z B : Scheme) (r : Z ⟶ B) (t : Z ⟶ Y) (p : X ⟶ Z)
      (b : Spec (.of A) ⟶ B) (u : B ⟶ Spec (.of R)) (M : Z.Modules),
      IsAffine B ∧ IsLocallyNoetherian B ∧ LocallyOfFinitePresentation u ∧
        IsPullback t r q u ∧ IsPullback p f r b ∧
        p ≫ t = a ∧ b ≫ u = Spec.map (CommRingCat.ofHom g) ∧
        LocallyFreeRankOne M ∧ Nonempty ((Scheme.Modules.pullback p).obj M ≅ L) := by
  let R₀ := g.toIntAlgHom.range
  let _ : Algebra.FiniteType ℤ R₀ := Algebra.FiniteType.of_surjective
    g.toIntAlgHom.rangeRestrict g.toIntAlgHom.rangeRestrict_surjective
  let k := Spec.map (CommRingCat.ofHom g.toIntAlgHom.rangeRestrict.toRingHom)
  let b₀ := Spec.map (CommRingCat.ofHom R₀.val.toRingHom)
  have hb₀ : b₀ ≫ k = Spec.map (CommRingCat.ofHom g) := by
    rw [← Spec.map_comp]
    rfl
  let q₀ := pullback.snd q k
  let a₀ := pullback.lift a (f ≫ b₀) (by rw [Category.assoc, hb₀]; exact H.w)
  have H₀ : IsPullback a₀ f q₀ b₀ := by
    apply IsPullback.of_right _ (by simp [a₀]) (IsPullback.of_hasPullback q k)
    simpa only [a₀, pullback.lift_fst, hb₀] using H
  obtain ⟨i, M, hM, he⟩ := exists_coefficient_independent_line_cartesian R₀ q₀ H₀ L hL
  let _ : Algebra.FiniteType ℤ i.unop.val := i.unop.property.2
  let _ : IsNoetherianRing i.unop.val := Algebra.FiniteType.isNoetherianRing ℤ i.unop.val
  let v := (coefficientSpectrumToInitial R₀).app i
  let u := v ≫ k
  have hu : LocallyOfFiniteType u := by
    change LocallyOfFiniteType (Spec.map _ ≫ Spec.map _)
    rw [← Spec.map_comp]
    apply HasRingHomProperty.Spec_iff.mpr
    apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap ℤ R)
    have heq : (((Subalgebra.inclusion i.unop.property.1).toRingHom.comp
        g.toIntAlgHom.rangeRestrict.toRingHom).comp (algebraMap ℤ R)) =
        algebraMap ℤ i.unop.val := by ext; simp
    change (((Subalgebra.inclusion i.unop.property.1).toRingHom.comp
      g.toIntAlgHom.rangeRestrict.toRingHom).comp (algebraMap ℤ R)).FiniteType
    rw [heq]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  let _ : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  let _ : LocallyOfFiniteType u := hu
  refine ⟨(coefficientModelDiagram R₀ q₀).obj i, Spec (.of i.unop.val),
    pullback.snd q₀ v, pullback.fst q₀ v ≫ pullback.fst q k,
    coefficientModelRecovery H₀ i, (coefficientSpectrumCone R₀).π.app i, u, M,
    inferInstance, inferInstance, inferInstance,
    (IsPullback.of_hasPullback q₀ v).paste_horiz (IsPullback.of_hasPullback q k),
    coefficientModelRecovery_isPullback H₀ i, ?_, ?_, hM, he⟩
  · rw [← Category.assoc, coefficientModelRecovery_fst]
    exact pullback.lift_fst _ _ _
  · rw [← Category.assoc, coefficientSpectrumCone_toInitial]
    exact hb₀

end FLT.Mazur.Approximation
