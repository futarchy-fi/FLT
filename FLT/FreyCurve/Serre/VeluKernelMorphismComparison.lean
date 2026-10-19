/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluKernelSectionComparison
public import FLT.Mazur.WeierstrassIntegralBaseChange

/-!
# The entire embedded kernel morphism commutes with descent

Coproduct extensionality upgrades the original component formulas to equality
of scheme morphisms. The resulting square is the actual coefficient pullback.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeierstrassCurve.Velu

open FLT.Mazur FLT.Mazur.WeierstrassIntegralChart

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime]
  (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →ₗ[ZMod p] ZMod p)
  (hq : Function.Surjective q)
  (hfixed : ∀ g t, q (E.torsionGaloisRepresentation p g t) = q t)

/-- The complete original geometric inclusion projects to the actual rational map. -/
@[reassoc] theorem primeKernelRationalMap_geometric :
    (primeKernelClosedSubgroup E p q hq).inclusion.left ≫ integralCoefficientMorphism E =
      (primeKernelPullbackIso E p q hq hfixed).hom ≫ pullback.snd _ _ ≫
        primeKernelRationalMap E p q hq hfixed := by
  apply (cancel_epi (ConstantCyclicFiniteEtale.underlyingIso (AlgebraicClosure ℚ) p).hom).mp
  apply Sigma.hom_ext
  intro i
  simp only [← Category.assoc, ConstantCyclicFiniteEtale.component_underlyingIso]
  rw [← Over.comp_left, primeKernelClosedSubgroup_component]
  rw [primeKernelRationalMap_section E p q hq hfixed i]
  simp only [Category.assoc, primeKernelPullbackIso_component_snd_assoc]

/-- The geometric subgroup is the Cartesian coefficient extension of its rational source. -/
theorem primeKernelRationalScheme_isPullback :
    IsPullback ((primeKernelPullbackIso E p q hq hfixed).hom ≫ pullback.snd _ _)
      (primeKernelClosedSubgroup E p q hq).carrier.hom
      (primeKernelRationalScheme E p q hq hfixed).hom
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) := by
  have h := (IsPullback.of_hasPullback
    (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))))
    (primeKernelRationalScheme E p q hq hfixed).hom
  refine h.flip.of_iso (primeKernelPullbackIso E p q hq hfixed).symm
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id, Iso.inv_hom_id_assoc]
  · rw [Iso.symm_hom, Iso.refl_hom, Category.comp_id,
      ← primeKernelPullbackIso_fst E p q hq hfixed, Iso.inv_hom_id_assoc]
  · simp
  · simp

/-- The embedded subgroup square itself is Cartesian, with its original inclusion. -/
theorem primeKernelRationalMap_isPullback :
    IsPullback (primeKernelClosedSubgroup E p q hq).inclusion.left
      ((primeKernelPullbackIso E p q hq hfixed).hom ≫ pullback.snd _ _)
      (integralCoefficientMorphism E) (primeKernelRationalMap E p q hq hfixed) := by
  apply IsPullback.of_right (h₁₂ := integralCurveStructure
    (E.map (algebraMap ℚ (AlgebraicClosure ℚ))))
    (h₂₂ := integralCurveStructure E)
    (v₁₃ := Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))
  · rw [primeKernelRationalMap_base]
    change IsPullback
      ((primeKernelClosedSubgroup E p q hq).inclusion.left ≫
        (integralGeneralizedEllipticCurve
          (E.map (algebraMap ℚ (AlgebraicClosure ℚ)))
          (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).isUnit_Δ).group.hom) _ _ _
    rw [(primeKernelClosedSubgroup E p q hq).inclusion.w]
    exact (primeKernelRationalScheme_isPullback E p q hq hfixed).flip
  · exact primeKernelRationalMap_geometric E p q hq hfixed
  · exact (integralCoefficient_isPullback E).flip

end WeierstrassCurve.Velu
