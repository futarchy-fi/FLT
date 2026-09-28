/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffinePullbackIdeal
public import FLT.Mazur.CartierChartFlat
public import FLT.Mazur.RelativeCartier

/-!
# Arbitrary base change of relative Cartier divisors

Flatness of the divisor quotient preserves regular equations after tensoring.
The affine section pushout identifies those equations with pullback sections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

variable {X S T : Scheme.{u}}

/-- On affine schemes, a regular equation with flat quotient stays regular after pullback. -/
theorem isRegular_pullback_fst_appTop [IsAffine X] [IsAffine S] [IsAffine T]
    (f : X ⟶ S) (g : T ⟶ S) (I : X.IdealSheafData)
    [Flat (I.subschemeι ≫ f)] (a : Γ(X, ⊤)) (ha : IsRegular a)
    (hI : I.ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span {a}) :
    IsRegular ((pullback.fst f g).appTop.hom a) := by
  let A := Γ(S, ⊤)
  let B := Γ(X, ⊤)
  let C := Γ(T, ⊤)
  let : Algebra A B := f.appTop.hom.toAlgebra
  let : Algebra A C := g.appTop.hom.toAlgebra
  have hq := flat_cartierChart_quotient f I ⟨⊤, isAffineOpen_top S⟩
    ⟨⊤, isAffineOpen_top X⟩ (by simp) a hI
  have hq' : (algebraMap A (B ⧸ Ideal.span {a})).Flat := by
    rw [IsScalarTower.algebraMap_eq A B (B ⧸ Ideal.span {a})]
    change ((Ideal.Quotient.mk (Ideal.span {a})).comp f.appTop.hom).Flat
    simpa [Scheme.Hom.appTop, Scheme.Hom.appLE] using hq
  let : Module.Flat A (B ⧸ Ideal.span {a}) := RingHom.flat_algebraMap_iff.mp hq'
  let H := isPushout_appTop_of_isPullback (IsPullback.of_hasPullback f g)
  let K := CommRingCat.isPushout_tensorProduct A B C
  let e := (K.isoIsPushout _ _ H).commRingCatIsoToRingEquiv
  have he : e (a ⊗ₜ[A] (1 : C)) = (pullback.fst f g).appTop.hom a := by
    exact congr($(K.inl_isoIsPushout_hom _ _ H).hom a)
  rw [← he]
  exact isRegular_tensor_equation (A := A) a ha C
    ((Algebra.TensorProduct.comm A C B).toRingEquiv.trans e)

/-- The top affine chart of a relative principal divisor survives arbitrary affine base change. -/
theorem cartierChart_pullback_top [IsAffine X] [IsAffine S] [IsAffine T]
    (f : X ⟶ S) (g : T ⟶ S) (I : X.IdealSheafData)
    [Flat (I.subschemeι ≫ f)] (hI : CartierChart I ⟨⊤, isAffineOpen_top X⟩) :
    CartierChart (I.comap (pullback.fst f g)) ⟨⊤, isAffineOpen_top (pullback f g)⟩ := by
  obtain ⟨a, ha, hIa⟩ := hI
  refine ⟨(pullback.fst f g).appTop.hom a,
    isRegular_pullback_fst_appTop f g I a ha hIa, ?_⟩
  rw [Scheme.IdealSheafData.ideal_comap_top, hIa, Ideal.map_span, Set.image_singleton]

/-- A global affine equation supplies a Cartier chart at every point. -/
lemma CartierChart.effectiveCartier_top [IsAffine X] {I : X.IdealSheafData}
    (hI : CartierChart I ⟨⊤, isAffineOpen_top X⟩) : EffectiveCartier I :=
  fun _ ↦ ⟨⟨⊤, isAffineOpen_top X⟩, trivial, hI⟩

/-- Restricting a Cartier chart gives a global equation on its affine scheme. -/
lemma CartierChart.comap_ι_top {I : X.IdealSheafData} {U : X.affineOpens}
    (hI : CartierChart I U) :
    CartierChart (I.comap U.1.ι) ⟨⊤, isAffineOpen_top U⟩ := by
  apply (cartierChart_comap_iff I U.1.ι _).mpr
  simpa using hI

/-- Over an affine base, source Cartier charts and target affine charts suffice. -/
theorem relativeCartierBaseChange_affineBase [IsAffine S]
    (f : X ⟶ S) (g : T ⟶ S) (I : X.IdealSheafData) :
    RelativeCartierBaseChange f g I := by
  intro hI
  classical
  let := hI.2
  choose U hx hU using hI.1
  let C := X.openCoverOfIsOpenCover (fun x ↦ (U x).1) (by
    change (⨆ x, (U x).1) = ⊤
    ext x
    exact ⟨fun _ ↦ trivial, fun _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩⟩)
  refine ⟨?_, hI.flat_baseChange g⟩
  apply (effectiveCartier_iff_openCover _
    (Scheme.Pullback.openCoverOfLeftRight C T.affineCover f g)).mpr
  rintro ⟨x, j⟩
  have : IsAffine (C.X x) := (U x).2
  have : Flat ((I.comap (C.f x)).subschemeι ≫ C.f x ≫ f) :=
    flat_comap_of_flat f (C.f x) I
  have hc : CartierChart (I.comap (C.f x)) ⟨⊤, isAffineOpen_top (C.X x)⟩ :=
    CartierChart.comap_ι_top (hU x)
  have h := (cartierChart_pullback_top (C.f x ≫ f) (T.affineCover.f j ≫ g)
    (I.comap (C.f x)) hc).effectiveCartier_top
  simpa only [Scheme.Pullback.openCoverOfLeftRight_f,
    ← Scheme.IdealSheafData.comap_comp, pullback.lift_fst] using h

/-- Relative effective Cartier divisors are preserved by arbitrary base change. -/
theorem relativeCartierBaseChange (f : X ⟶ S) (g : T ⟶ S)
    (I : X.IdealSheafData) : RelativeCartierBaseChange f g I := by
  intro hI
  refine ⟨?_, hI.flat_baseChange g⟩
  apply (effectiveCartier_iff_openCover _
    (Scheme.Pullback.openCoverOfBase S.affineCover f g)).mpr
  intro i
  have hi : RelativeEffectiveCartier (pullback.snd f (S.affineCover.f i))
      (I.comap (pullback.fst f (S.affineCover.f i))) :=
    ⟨hI.1.comap_of_isOpenImmersion _, hI.flat_baseChange _⟩
  have h := relativeCartierBaseChange_affineBase
    (pullback.snd f (S.affineCover.f i)) (pullback.snd g (S.affineCover.f i))
    (I.comap (pullback.fst f (S.affineCover.f i))) hi
  simpa only [Scheme.Pullback.openCoverOfBase_f,
    ← Scheme.IdealSheafData.comap_comp, pullback.lift_fst] using h.1

end FLT.Mazur.FCurve
