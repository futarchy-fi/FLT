/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertRelationOperations

/-!
# Whole-fiber affine neighborhoods in the actual restricted relation

Both endpoints remain étale and have finite fibers. The affine product
envelope provides a common affine neighborhood of each entire endpoint
fiber, inside any prescribed open. Endpoint coordinate algebras on these
neighborhoods are finitely presented over the original affine source.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left]
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k

instance snd_etale : Etale (q).left := by
  let _ : Etale (prod.fst : prod A V ⟶ A).left := by
    rw [← Over.prodLeftIsoPullback_hom_fst A V]
    infer_instance
  rw [← toEnvelope_test f hL d V c k, Over.comp_left]
  infer_instance

instance fst_etale : Etale (p).left := by
  let e := (Over.forget _).mapIso (swapIso f hL d V c k)
  have h : e.hom ≫ (q).left = (p).left :=
    congrArg Over.Hom.left (equivalence f hL d V c k).symmetry₂
  rw [← h]
  infer_instance

/-- The second endpoint retains a finite FULL fiber after restricting both source endpoints. -/
theorem snd_finite_fiber (x : A.left) : ((q).left ⁻¹' {x}).Finite := by
  let s := sectionAt f hL d V c k
  let u := variableHilbertOverlapToChart f d hL V c A s
  let j := (pullback.fst u k).left
  let _ : IsOpenImmersion j :=
    MorphismProperty.of_isPullback ((IsPullback.of_hasPullback u k).map (Over.forget _)).flip
      (inferInstanceAs (IsOpenImmersion k.left))
  change (j ⁻¹' ((variableHilbertOverlapToTest f d V c A s).left ⁻¹' {x})).Finite
  exact (variableHilbertOverlapToTest_finite_fiber f d V c A s x).preimage j.injective.injOn

/-- Inversion retains the entire finite first endpoint fiber. -/
theorem fst_finite_fiber (x : A.left) : ((p).left ⁻¹' {x}).Finite := by
  let e := (Over.forget _).mapIso (swapIso f hL d V c k)
  have h : e.hom ≫ (q).left = (p).left :=
    congrArg Over.Hom.left (equivalence f hL d V c k).symmetry₂
  rw [← h]
  change (e.hom ⁻¹' ((q).left ⁻¹' {x})).Finite
  exact (snd_finite_fiber f hL d V c k x).preimage e.hom.injective.injOn

variable [IsAffine A.left]

omit [Etale V.hom] in
/-- Any finite set of actual relation arrows has a common affine neighborhood inside any open. -/
theorem exists_affine_neighborhood (W : (relation f hL d V c k).left.Opens)
    (t : Set (relation f hL d V c k).left) (ht : t.Finite) (htW : t ⊆ W) :
    ∃ U : (relation f hL d V c k).left.Opens, IsAffineOpen U ∧ t ⊆ U ∧ U ≤ W := by
  let _ := variableHilbertOverlap_envelope_affine V A
  exact AffineEnvelopeFiniteNeighborhood.exists_affineOpen
    (toEnvelope f hL d V c k).left W t ht htW

/-- A single affine neighborhood contains BOTH complete endpoint fibers at an original point. -/
theorem exists_endpoint_fibers_affine_neighborhood (x : A.left)
    (W : (relation f hL d V c k).left.Opens)
    (hW : (p).left ⁻¹' {x} ∪ (q).left ⁻¹' {x} ⊆ W) :
    ∃ U : (relation f hL d V c k).left.Opens,
      IsAffineOpen U ∧ (p).left ⁻¹' {x} ∪ (q).left ⁻¹' {x} ⊆ U ∧ U ≤ W :=
  exists_affine_neighborhood f hL d V c k W _
    ((fst_finite_fiber f hL d V c k x).union (snd_finite_fiber f hL d V c k x)) hW

omit [IsAffine V.left] in
/-- Both actual endpoint maps give finitely presented coefficient algebras on affine opens. -/
theorem endpoint_finitePresentation (U : (relation f hL d V c k).left.affineOpens) :
    (U.val.ι ≫ (p).left).appTop.hom.FinitePresentation ∧
      (U.val.ι ≫ (q).left).appTop.hom.FinitePresentation := by
  let _ : IsAffine U.val := U.property
  exact ⟨(U.val.ι ≫ (p).left).finitePresentation_appTop,
    (U.val.ι ≫ (q).left).finitePresentation_appTop⟩

end FLT.Mazur.HilbertChart.AffineRestriction
