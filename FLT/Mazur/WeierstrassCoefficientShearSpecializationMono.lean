/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearSpecialization
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The residue tangent gluing embeds in the integral tangent gluing

Surjective original coefficients give a surjective tangent-root map. Its
monomorphism on spectra makes the actual specialization of whole gluings
monic, so it preserves their full component intersections.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R T : Type u} [CommRing R] [CommRing T]
  (W : WeierstrassCurve R) (f : R →+* T)

/-- Every function on the specialized tangent algebra lifts when original coefficients lift. -/
theorem tangentCoefficientMap_surjective (hf : Function.Surjective f) :
    Function.Surjective (nodeTangentCoefficientMap W f) := by
  intro z
  induction z using AdjoinRoot.induction_on with
  | ih p =>
    obtain ⟨q, rfl⟩ := Polynomial.map_surjective f hf p
    refine ⟨AdjoinRoot.mk (nodeTangentPolynomial W) q, ?_⟩
    rw [nodeTangentCoefficientMap, AdjoinRoot.map, AdjoinRoot.lift_mk,
      ← Polynomial.eval₂_map, ← AdjoinRoot.algebraMap_eq, ← Polynomial.aeval_def]
    exact AdjoinRoot.aeval_eq _

variable [IsDomain R] [IsBezout R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] [Algebra R T]
  (r : S) (v : T) (j : ℕ) (hj : j ≤ n) (g : S →ₐ[R] T)
local notation "b" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom g))

/-- A monic coefficient specialization gives a monic map of the complete equation gluings. -/
instance coefficientShearSpecialization_mono [Mono b] :
    Mono (coefficientShearSpecialization hπ data S T r v j hj g) where
  right_cancellation := by
    intro Z f₁ f₂ he
    apply (coefficientShearGlued_isPullback hπ data T v j hj).hom_ext
    · apply (cancel_mono b).mp
      have h := congrArg (fun f => f ≫ coefficientShearGluedStructure hπ data S r j hj) he
      simpa only [Category.assoc, coefficientShearSpecialization_structure] using h
    · have h := congrArg (fun f => f ≫ coefficientShearGluedProjection hπ data S r j hj) he
      simpa only [Category.assoc, coefficientShearSpecialization_projection] using h

variable [IsLocalRing R]

/-- The real residue tangent spectrum is a closed subscheme of the integral tangent spectrum. -/
instance tangentResidueCoefficient_isClosedImmersion :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (nodeTangentCoefficientMap W (residue R)))) :=
  IsClosedImmersion.spec_of_surjective _
    (tangentCoefficientMap_surjective W (residue R) residue_surjective)

/-- Specialization retains full intersections inside the original integral tangent gluing. -/
instance coefficientShearTangentSpecialization_mono :
    Mono (coefficientShearTangentSpecialization hπ data j hj) := by
  let _ : Mono (Spec.map (CommRingCat.ofHom
      (tangentResidueCoefficientAlgHom (W := W)).toRingHom)) :=
    inferInstanceAs (Mono (Spec.map (CommRingCat.ofHom
      (nodeTangentCoefficientMap W (residue R)))))
  unfold coefficientShearTangentSpecialization
  infer_instance

end FLT.Mazur.WeierstrassDividedDepth
