/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ConstantCyclicGroup
public import FLT.Mazur.ConstantDegree
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Finite etale degree of the constant cyclic group

The actual coproduct group over a commutative ring is identified over its base with
the spectrum of its product algebra. This proves degree n. Etaleness follows
on its open components, each of which maps identically to the base.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

namespace FLT.Mazur.ConstantCyclicAffineGeometry

variable (K : Type) [CommRing K] (n : ℕ) [NeZero n]

local notation "S" => Spec (CommRingCat.of K)
local notation "D" => ConstantCyclicGroup.model S n

/-- Forgetting the over-category coproduct retains the actual base components. -/
def underlyingIso : (∐ fun _ : ZMod n ↦ S) ≅ (D).left :=
  asIso (sigmaComparison (Over.forget S) (fun _ : ZMod n ↦ 𝟙_ (Over S)))

/-- The underlying comparison maps each component to its specified inclusion. -/
@[reassoc]
theorem component_underlyingIso (i : ZMod n) :
    Sigma.ι _ i ≫ (underlyingIso K n).hom =
      (ConstantCyclicGroup.component S n i).left :=
  ι_comp_sigmaComparison (Over.forget S) (fun _ : ZMod n ↦ 𝟙_ (Over S)) i

/-- The product algebra is a global coordinate ring of the constant group. -/
def coordinateIso : (D).left ≅ Spec (.of (ZMod n → K)) :=
  (underlyingIso K n).symm ≪≫ asIso (sigmaSpec (fun _ : ZMod n ↦ .of K))

/-- The coordinate isomorphism retains the structure map to the base ring. -/
@[reassoc]
theorem coordinateIso_base :
    (coordinateIso K n).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (ZMod n → K))) = (D).hom := by
  apply (cancel_epi (underlyingIso K n).hom).mp
  apply Sigma.hom_ext
  intro i
  simp only [coordinateIso, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    Category.assoc, Iso.hom_inv_id_assoc, ι_sigmaSpec_assoc, component_underlyingIso_assoc]
  rw [← Spec.map_comp]
  change Spec.map (𝟙 (CommRingCat.of K)) = _
  rw [Spec.map_id]
  exact (ConstantCyclicGroup.component S n i).w.symm

/-- The coordinate comparison is an isomorphism over the ring. -/
def coordinateOverIso : D ≅
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (ZMod n → K)))) :=
  Over.isoMk (coordinateIso K n) (coordinateIso_base K n)

/-- The constant cyclic group has finite locally free degree n. -/
theorem degree : FCurve.FiniteLocallyFreeDegree (D).hom n := by
  apply (FCurve.finiteLocallyFreeDegree_iff_of_overIso (coordinateOverIso K n)).mpr
  change FCurve.FiniteLocallyFreeDegree
    (Spec.map (CommRingCat.ofHom (algebraMap K (ZMod n → K)))) n
  refine ⟨?_, ?_, ?_, fun x ↦ ?_⟩
  · rw [IsFinite.SpecMap_iff]
    change (algebraMap K (ZMod n → K)).Finite
    rw [RingHom.finite_algebraMap]
    infer_instance
  · rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    change (algebraMap K (ZMod n → K)).Flat
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  · rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
    change (algebraMap K (ZMod n → K)).FinitePresentation
    rw [RingHom.finitePresentation_algebraMap]
    infer_instance
  · let _ : Nontrivial K := x.nontrivial
    rw [Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
    simp

/-- The constant cyclic group is etale, even in characteristic dividing n. -/
theorem etale : Etale (D).hom := by
  have he : (underlyingIso K n).hom ≫ (D).hom = Sigma.desc (fun _ : ZMod n ↦ 𝟙 S) := by
    apply Sigma.hom_ext
    intro i
    rw [component_underlyingIso_assoc, Sigma.ι_comp_desc]
    exact (ConstantCyclicGroup.component S n i).w
  have : Etale ((underlyingIso K n).hom ≫ (D).hom) := by
    rw [he]
    exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale) fun _ ↦ inferInstance
  exact (MorphismProperty.cancel_left_of_respectsIso (@Etale) (underlyingIso K n).hom (D).hom).mp
    inferInstance

end FLT.Mazur.ConstantCyclicAffineGeometry
