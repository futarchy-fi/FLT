/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ArithmeticTensorResidueCover
public import FLT.Mazur.WeierstrassSuccessiveXAnyDepthSmoothCover
public import FLT.Mazur.WeierstrassSuccessiveXTensorStructure
public import FLT.Mazur.SchemeSmoothLocusCartesian

/-!
# Smooth coverage of the actual arithmetic successive chart

The residue criterion detects smoothness on every arithmetic thickening when
the original parameter generates the maximal ideal. The two tests use the
original incidence and horizontal coordinates, including at creation depth zero.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassSuccessiveX
open PolygonArithmeticStages
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (hπ : π ≠ 0) (hgen : maximalIdeal R = ideal R π)
  (k : ℕ) (hk : 2 * (k + 1) ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4) (m : ℕ)
local notation "Q" => Quotient R π m
local notation "F" => ResidueField R
local notation "C" => Coordinate W (π ^ k) π b3 b4 b6
local notation "T" => ScalarExtension W (π ^ k) π b3 b4 b6 Q
local notation "T₀" => ScalarExtension W (π ^ k) π b3 b4 b6 F
local notation "s" => Spec.map (CommRingCat.ofHom (algebraMap Q T))
local notation "s₀" => Spec.map (CommRingCat.ofHom (algebraMap F T₀))
local notation "t" => tensorCoord W (π ^ k) π b3 b4 b6 Q 0
local notation "v" => tensorCoord W (π ^ k) π b3 b4 b6 Q 2

include D hπ hgen hk h3 h4 in
/-- The full arithmetic smooth locus is exactly the union of the two original boundaries. -/
theorem arithmeticAnyDepth_mem_smooth_iff (p : Spec (.of T)) :
    p ∈ (s).smoothLocus ↔ t ∉ p.asIdeal ∨ v ∉ p.asIdeal := by
  let hres := parameter_residue_zero R π hgen
  let f := residueAlgHom R π hres m
  obtain ⟨q, hq, hc⟩ := exists_tensorResidue_lift R π hres m C hgen p
  let _ : Flat (Spec.map (CommRingCat.ofHom (algebraMap Q (Q ⊗[R] C)))) :=
    successiveTensorStructure_flat W (π ^ k) π b3 b4 b6 Q hπ
  let _ : LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (algebraMap Q (Q ⊗[R] C)))) :=
    successiveTensorStructure_finitePresentation W (π ^ k) π b3 b4 b6 Q
  let _ : LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (algebraMap F (F ⊗[R] C)))) :=
    successiveTensorStructure_finitePresentation W (π ^ k) π b3 b4 b6 F
  have he := smoothLocus_preimage_of_isPullback
    (TensorCoefficientMap.spectrum_isPullback (A := C) f)
  have hs : p ∈ (s).smoothLocus ↔ q ∈ (s₀).smoothLocus := by
    rw [← hq]
    change q ∈ (TensorCoefficientMap.spectrum f ⁻¹ᵁ (s).smoothLocus) ↔ _
    exact (congrArg (fun U => q ∈ U) he).to_iff
  have hr := residueAnyDepth_mem_smooth_iff D k hk b3 b4 b6 h3 h4
    (𝟙 (Spec (.of T₀))) s₀ (by rw [Category.id_comp]) q
  have hb : t ∉ p.asIdeal ∨ v ∉ p.asIdeal ↔
      tensorCoord W (π ^ k) π b3 b4 b6 F 0 ∉ q.asIdeal ∨
        tensorCoord W (π ^ k) π b3 b4 b6 F 2 ∉ q.asIdeal :=
    or_congr (not_congr (hc _)) (not_congr (hc _))
  exact hs.trans (hr.trans hb.symm)

variable {X : Scheme.{u}}
  (g : Spec (.of (ScalarExtension W (π ^ k) π b3 b4 b6 (Quotient R π m))) ⟶ X)
  [IsOpenImmersion g] (base : X ⟶ Spec (.of (Quotient R π m)))
  [LocallyOfFinitePresentation base]
  (hg : g ≫ base = Spec.map (CommRingCat.ofHom (algebraMap (Quotient R π m)
    (ScalarExtension W (π ^ k) π b3 b4 b6 (Quotient R π m)))))

include D hπ hgen hk h3 h4 hg in
/-- The same exact two-coordinate criterion holds in every actual ambient open chart. -/
theorem arithmeticAnyDepth_chart_mem_smooth_iff (p : Spec (.of T)) :
    g p ∈ base.smoothLocus ↔ t ∉ p.asIdeal ∨ v ∉ p.asIdeal := by
  have he := PolygonAtlas.mem_smooth_iff g base p
  simp only [hg] at he
  exact he.trans (arithmeticAnyDepth_mem_smooth_iff D hπ hgen k hk b3 b4 b6 h3 h4 m p)

include D hπ hgen hk h3 h4 hg in
/-- A smooth nonpunctured arithmetic input satisfies the original incidence condition. -/
theorem arithmeticAnyDepth_chart_incidence_nonzero (p : Spec (.of T))
    (hs : g p ∈ base.smoothLocus) (hz : v ∈ p.asIdeal) : t ∉ p.asIdeal := by
  have he := (arithmeticAnyDepth_chart_mem_smooth_iff D hπ hgen k hk b3 b4 b6
    h3 h4 m g base hg p).mp hs
  exact he.resolve_right (not_not.mpr hz)

end FLT.Mazur.WeierstrassSuccessiveX
