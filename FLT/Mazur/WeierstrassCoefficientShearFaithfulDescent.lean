/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearActionDomainTransport
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Effective descent from the original full coefficient equation model

A faithfully flat coefficient extension makes both the actual model projection
and its full action-domain projection effective epimorphisms. Compatible scheme
maps therefore descend uniquely, with no assumption of a split special fiber.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (r : S) (j : ℕ) (hj : j ≤ n)
  (hS : (algebraMap R S).FaithfullyFlat)
local notation "p" => coefficientShearGluedProjection hπ data S r j hj
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "P" => coefficientShearOriginalActionProduct hπ data S r j hj

include hS in
/-- The original coefficient equation gluing effectively covers its integral model. -/
theorem coefficientShearGluedProjection_effectiveEpi : EffectiveEpi p := by
  obtain ⟨hq, hq'⟩ := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap R S))).mpr hS
  have H := coefficientShearGlued_isPullback hπ data S r j hj
  let _ : Flat p := MorphismProperty.of_isPullback H hq
  let _ : Surjective p := MorphismProperty.of_isPullback H hq'
  let _ : QuasiCompact p := MorphismProperty.of_isPullback H (inferInstance : QuasiCompact q)
  infer_instance

include hS in
/-- The full pair of equation inputs effectively covers the original action domain. -/
theorem coefficientShearOriginalActionProduct_effectiveEpi : EffectiveEpi P := by
  obtain ⟨hq, hq'⟩ := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap R S))).mpr hS
  have H := (coefficientShearActionDomain_coefficient_isPullback hπ data S r j hj).flip
  let _ : Flat P := MorphismProperty.of_isPullback H hq
  let _ : Surjective P := MorphismProperty.of_isPullback H hq'
  let _ : QuasiCompact P := MorphismProperty.of_isPullback H (inferInstance : QuasiCompact q)
  infer_instance

include hS in
/-- Every compatible map on the full equation model descends to a unique integral map. -/
theorem coefficientShearGluedProjection_existsUnique {Y : Scheme.{u}}
    (k : coefficientShearGlued hπ data S r j hj ⟶ Y)
    (hk : pullback.fst p p ≫ k = pullback.snd p p ≫ k) :
    ∃! t : finiteGlobalModel hπ data j hj ⟶ Y, p ≫ t = k := by
  let _ := coefficientShearGluedProjection_effectiveEpi hπ data S r j hj hS
  let C := isColimitCoforkOfEffectiveEpi p (IsPullback.of_hasPullback p p).cone
    (IsPullback.of_hasPullback p p).isLimit
  exact ⟨C.desc (Cofork.ofπ k hk), Cofork.IsColimit.π_desc C,
    fun _ ht => (cancel_epi p).mp
      (ht.trans (Cofork.IsColimit.π_desc (t := Cofork.ofπ k hk) C).symm)⟩

include hS in
/-- A compatible map on both actual inputs descends uniquely on the full integral domain. -/
theorem coefficientShearOriginalActionProduct_existsUnique {Y : Scheme.{u}}
    (k : coefficientShearActionDomain hπ data S r j hj ⟶ Y)
    (hk : pullback.fst P P ≫ k = pullback.snd P P ≫ k) :
    ∃! t : finiteGlobalActionProduct hπ data j hj ⟶ Y, P ≫ t = k := by
  let _ := coefficientShearOriginalActionProduct_effectiveEpi hπ data S r j hj hS
  let C := isColimitCoforkOfEffectiveEpi P (IsPullback.of_hasPullback P P).cone
    (IsPullback.of_hasPullback P P).isLimit
  exact ⟨C.desc (Cofork.ofπ k hk), Cofork.IsColimit.π_desc C,
    fun _ ht => (cancel_epi P).mp
      (ht.trans (Cofork.IsColimit.π_desc (t := Cofork.ofπ k hk) C).symm)⟩

end FLT.Mazur.WeierstrassDividedDepth
