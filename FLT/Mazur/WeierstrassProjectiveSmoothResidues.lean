/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassProjectiveRelativeSmoothCriterion

/-!
# Residue tests for projective smoothness over arbitrary algebras

At any source prime, the image in a normalized chart is relatively smooth
exactly when the induced coordinates over that source residue field are
nonsingular. This supplies local input and output tests for projective addition.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (j : Fin 3) (f : Coordinate W j →ₐ[R] S)
  (p : PrimeSpectrum S)

/-- The residue chart map is the original chart map after the source residue morphism. -/
theorem chartResidue_spec :
    Spec.map (CommRingCat.ofHom
      ((IsScalarTower.toAlgHom R S p.asIdeal.ResidueField).comp f).toRingHom) =
      Spec.map (CommRingCat.ofHom (algebraMap S p.asIdeal.ResidueField)) ≫
        Spec.map (CommRingCat.ofHom f.toRingHom) := by
  rw [← Spec.map_comp]
  rfl

/-- Smoothness at a source prime gives nonsingularity over that prime's residue field. -/
theorem chartAlgebra_residue_nonsingular_at
    (hp : (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ integralCurveChart W j) p ∈
      integralSmoothOpen W) :
    let g := (IsScalarTower.toAlgHom R S p.asIdeal.ResidueField).comp f
    (W.map (algebraMap R p.asIdeal.ResidueField)).toProjective.Nonsingular (g ∘ coord W j) := by
  apply chartFieldPoint_nonsingular_of_smooth W j
  rw [chartResidue_spec, Category.assoc]
  rintro _ ⟨z, rfl⟩
  have hz : PrimeSpectrum.comap (algebraMap S p.asIdeal.ResidueField) z = p :=
    Set.mem_singleton_iff.mp ((PrimeSpectrum.residueField_comap p) ▸ Set.mem_range_self z)
  change (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ integralCurveChart W j)
    (PrimeSpectrum.comap (algebraMap S p.asIdeal.ResidueField) z) ∈ _
  rwa [hz]

/-- Nonsingularity over a source residue field puts its image in the actual smooth open. -/
theorem chartAlgebra_smooth_at_of_residue
    (hp : let g := (IsScalarTower.toAlgHom R S p.asIdeal.ResidueField).comp f
      (W.map (algebraMap R p.asIdeal.ResidueField)).toProjective.Nonsingular (g ∘ coord W j)) :
    (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ integralCurveChart W j) p ∈
      integralSmoothOpen W := by
  have h := chartFieldPoint_range_smooth W j
    ((IsScalarTower.toAlgHom R S p.asIdeal.ResidueField).comp f) hp
  rw [chartResidue_spec, Category.assoc] at h
  let z : Spec (.of p.asIdeal.ResidueField) := ⟨⊥, inferInstance⟩
  have hz : PrimeSpectrum.comap (algebraMap S p.asIdeal.ResidueField) z = p :=
    Set.mem_singleton_iff.mp ((PrimeSpectrum.residueField_comap p) ▸ Set.mem_range_self z)
  have hm := h ⟨z, rfl⟩
  change (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ integralCurveChart W j)
    (PrimeSpectrum.comap (algebraMap S p.asIdeal.ResidueField) z) ∈ _ at hm
  rwa [hz] at hm

/-- Relative smoothness of every chart image has an exact source-residue test. -/
theorem chartAlgebra_smooth_at_iff :
    (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ integralCurveChart W j) p ∈
        integralSmoothOpen W ↔
      (W.map (algebraMap R p.asIdeal.ResidueField)).toProjective.Nonsingular
        (((IsScalarTower.toAlgHom R S p.asIdeal.ResidueField).comp f) ∘ coord W j) :=
  ⟨chartAlgebra_residue_nonsingular_at W j f p, chartAlgebra_smooth_at_of_residue W j f p⟩

end FLT.Mazur.WeierstrassIntegralChart
