/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeSmoothLocus

/-!
# Relative jet obstructions over an arbitrary coefficient ring

A nonliftable residue-field tangent vector obstructs formal smoothness of
its origin localization even when the coefficient ring is not a field.
We also pass from the scheme smooth locus to the corresponding localized algebra.
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.StructureSheaf CategoryTheory

namespace FLT.Mazur.PolygonNodePresentation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R S K : Type u} [CommRing R] [CommRing S] [Field K]
  [Algebra R S] [Algebra R K]

/-- Scheme-theoretic smoothness on a spectrum implies smoothness of its localized algebra. -/
theorem spec_smooth_implies_algebra
    [LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R S)))]
    (p : PrimeSpectrum S)
    (hp : p ∈ (Spec.map (CommRingCat.ofHom (algebraMap R S))).smoothLocus) :
    p ∈ Algebra.smoothLocus R S := by
  let q := PrimeSpectrum.comap (algebraMap R S) p
  let T := (structurePresheafInCommRingCat S).stalk p
  let : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra
  let : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  have hR : (toStalk R q).hom.FormallySmooth := by
    rw [show (toStalk R q).hom = algebraMap R _ from rfl,
      RingHom.formallySmooth_algebraMap]
    exact Algebra.FormallySmooth.of_isLocalization q.asIdeal.primeCompl
  have h := hR.comp hp
  rw [← CommRingCat.hom_comp] at h
  erw [stalkMap_toStalk (CommRingCat.ofHom (algebraMap R S)) p] at h
  rw [CommRingCat.hom_comp] at h
  have ht : Algebra.FormallySmooth R T := RingHom.formallySmooth_algebraMap.mp h
  exact (Algebra.FormallySmooth.iff_of_equiv ((stalkIso S p).restrictScalars R)).mpr ht

/-- A residue-field tangent obstruction survives localization over an arbitrary base. -/
theorem relativeJet_origin_not_formallySmooth
    (p : Ideal S) [p.IsPrime] (e : S →ₐ[R] K) (f : S →ₐ[R] Jet K 2)
    (hker : RingHom.ker e.toRingHom = p)
    (he : ((jetEval (K := K)).restrictScalars R).comp f = e)
    (hn : ∀ g : S →ₐ[R] Jet K 3, ((jetDrop (K := K)).restrictScalars R).comp g ≠ f) :
    ¬ Algebra.FormallySmooth R (Localization.AtPrime p) := by
  intro h
  let _ := h
  let L := Localization.AtPrime p
  have hu (y : p.primeCompl) : IsUnit (f y) := by
    apply jet_isUnit
    change (((jetEval (K := K)).restrictScalars R).comp f) y ≠ 0
    rw [he]
    exact fun hzero ↦ y.property (hker ▸ hzero)
  let F : L →ₐ[R] Jet K 2 := IsLocalization.liftAlgHom hu
  let G := Algebra.FormallySmooth.liftOfSurjective F ((jetDrop (K := K)).restrictScalars R)
    jetDrop_surjective
    (show IsNilpotent (RingHom.ker (jetDrop (K := K)).toRingHom) from ⟨2, jetDrop_ker_sq⟩)
  apply hn (G.comp (IsScalarTower.toAlgHom R S L))
  ext z
  change ((jetDrop (K := K)).restrictScalars R) (G (algebraMap S L z)) = f z
  rw [Algebra.FormallySmooth.liftOfSurjective_apply]
  exact IsLocalization.lift_eq hu z

end FLT.Mazur.PolygonNodePresentation
