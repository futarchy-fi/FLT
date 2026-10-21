/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInputNonsingular
public import FLT.Mazur.WeierstrassDividedSuppliedOriginalSmoothAddition

/-!
# Full original-smooth coverage of punctured zero-depth pairs

Both actual contractions are smooth at every punctured closed-fiber input.
Consequently the original smooth law supplies a resolved output for all such
pairs, including equal points and self-inverse points in every characteristic.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing WeierstrassCurve
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  [CommRing S] [Algebra R S] {W : WeierstrassCurve R} {π : R} {m : ℕ}
  (D : SplitNodeDepth W π m) (d : Data W π 0)
  (a : Coordinate W (π ^ 0) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "f" => Spec.map (CommRingCat.ofHom a.toRingHom) ≫ toCurve d
local notation "x₀" => WeierstrassIntegralChart.coord W 2 0
local notation "y₀" => WeierstrassIntegralChart.coord W 2 1

include D

/-- A punctured scale-one input belongs to the actual original smooth inverse image. -/
theorem zeroDepthInput_originalSmooth_mem (hm : 0 < m) (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal)
    (hx : a (x W (π ^ 0) d.b3 d.b4 d.b6) ∉ p.asIdeal) :
    p ∈ f ⁻¹ᵁ WeierstrassIntegralChart.integralSmoothOpen W := by
  let ρ : S →ₐ[R] p.asIdeal.ResidueField := IsScalarTower.toAlgHom R S _
  let A := (ρ.comp a).comp
    (fromOriginal W (π ^ 0) d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6)
  have hπ : algebraMap R p.asIdeal.ResidueField π = 0 := by
    rw [IsScalarTower.algebraMap_apply R S p.asIdeal.ResidueField]
    exact Ideal.algebraMap_residueField_eq_zero.mpr hp
  have hn := zeroDepthInput_nonsingular D d (ρ.comp a) hm hπ
    (fun h => hx (Ideal.algebraMap_residueField_eq_zero.mp h))
  have hA : A ∘ WeierstrassIntegralChart.coord W 2 = ![A x₀, A y₀, 1] := by
    funext i
    fin_cases i <;> simp
  have hr := WeierstrassIntegralChart.chartFieldPoint_range_smooth W 2 A
    (by rw [hA]; exact (Projective.nonsingular_some _ _).mpr hn)
  have he : Spec.map (CommRingCat.ofHom ρ.toRingHom) ⟨⊥, inferInstance⟩ = p := by
    apply PrimeSpectrum.ext
    apply Ideal.ext
    intro z
    change algebraMap S p.asIdeal.ResidueField z = 0 ↔ z ∈ p.asIdeal
    exact Ideal.algebraMap_residueField_eq_zero
  have hf : Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ f =
      Spec.map (CommRingCat.ofHom A.toRingHom) ≫
        WeierstrassIntegralChart.integralCurveChart W 2 := by
    simp only [toCurve, WeierstrassDilatation.toCurve, ← Category.assoc, ← Spec.map_comp]
    rfl
  rw [← hf] at hr
  exact hr ⟨⟨⊥, inferInstance⟩, by rw [Scheme.Hom.comp_apply, he]⟩

/-- All punctured zero-depth pairs lie in the actual domain, including vertical tangents. -/
theorem suppliedOriginalSmoothDomain_zero_mem
    (c : Coordinate W (π ^ 0) d.b3 d.b4 d.b6 →ₐ[R] S) (hm : 0 < m)
    (p : PrimeSpectrum S) (hp : algebraMap R S π ∈ p.asIdeal)
    (hx : a (x W (π ^ 0) d.b3 d.b4 d.b6) ∉ p.asIdeal)
    (hu : c (x W (π ^ 0) d.b3 d.b4 d.b6) ∉ p.asIdeal) :
    p ∈ suppliedOriginalSmoothDomain d a c :=
  ⟨zeroDepthInput_originalSmooth_mem D d a hm p hp hx,
    zeroDepthInput_originalSmooth_mem D d c hm p hp hu⟩

/-- Transport the full coverage statement across a supplied depth equality. -/
theorem suppliedOriginalSmoothDomain_zeroDepth_mem {k : ℕ} (e : Data W π k)
    (a c : Coordinate W (π ^ k) e.b3 e.b4 e.b6 →ₐ[R] S) (hk : k = 0) (hm : 0 < m)
    (p : PrimeSpectrum S) (hp : algebraMap R S π ∈ p.asIdeal)
    (hx : a (x W (π ^ k) e.b3 e.b4 e.b6) ∉ p.asIdeal)
    (hu : c (x W (π ^ k) e.b3 e.b4 e.b6) ∉ p.asIdeal) :
    p ∈ suppliedOriginalSmoothDomain e a c := by
  subst k
  exact suppliedOriginalSmoothDomain_zero_mem D e a c hm p hp hx hu

end FLT.Mazur.WeierstrassDividedDepth
