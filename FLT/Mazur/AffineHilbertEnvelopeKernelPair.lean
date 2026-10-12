/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertEnvelopeScheme

/-!
# The original Hilbert relation is the constructed affine quotient's kernel pair

The full envelope square and affine reconstruction identify the ORIGINAL two
endpoints as a scheme kernel pair. No replacement relation is used.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve Approximation SchemeRelationTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left] (k : A ⟶ variableHilbertTest f d V)
local notation "Z" => relation f hL d V c k
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "j" => toEnvelope f hL d V c k
local notation "β" => k ≫ variableHilbertBase f d V
/-- The source's original structural algebra. -/
local instance kernelSourceAlgebra : Algebra R Γ(A.left, ⊤) := affineBaseSectionAlgebra A.hom
/-- The translation base's original structural algebra. -/
local instance kernelBaseAlgebra : Algebra R Γ(V.left, ⊤) := affineBaseSectionAlgebra V.hom
variable [IsIso (toEnvelope f hL d V c k).left]

/-- The constructed projection equalizes both ORIGINAL full relation endpoints. -/
theorem fullEnvelopeProjection_equalizes :
    (p).left ≫ fullEnvelopeProjection f hL d V c k =
      (q).left ≫ fullEnvelopeProjection f hL d V c k := by
  let _ := coefficientAlgebra β
  let _ := coefficientTower β
  let _ := fullEnvelope_relation_affine f hL d V c k
  change (p).left ≫ A.left.isoSpec.hom ≫ Spec.map _ =
    (q).left ≫ A.left.isoSpec.hom ≫ Spec.map _
  rw [← Scheme.isoSpec_hom_naturality_assoc, ← Scheme.isoSpec_hom_naturality_assoc,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro b
  exact (fullEnvelopeData_fixed_iff f hL d V c k b.val).mp b.property

omit [IsAffine V.left] [IsAffine A.left] in
/-- The original envelope is the cartesian square retaining both independent base maps. -/
theorem fullEnvelope_base_isPullback :
    IsPullback (p ≫ β).left (q).left V.hom A.hom := by
  have H : IsPullback (prod.fst : prod A V ⟶ A).left
      (prod.snd : prod A V ⟶ V).left A.hom V.hom :=
    Over.isPullback_of_binaryFan_isLimit
    (BinaryFan.mk (prod.fst : prod A V ⟶ A) (prod.snd : prod A V ⟶ V)) (prodIsProd A V)
  apply H.flip.of_iso' (asIso (j).left) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simpa only [asIso_hom, Iso.refl_hom, Category.comp_id, Over.comp_left] using
      congrArg Over.Hom.left (toEnvelope_base f hL d V c k)
  · simpa only [asIso_hom, Iso.refl_hom, Category.comp_id, Over.comp_left] using
      congrArg Over.Hom.left (toEnvelope_test f hL d V c k)
  · simp
  · simp

/-- The ORIGINAL full relation is the constructed scheme projection's complete kernel pair. -/
theorem fullEnvelope_kernelPair [Flat V.hom] :
    IsPullback (p).left (q).left (fullEnvelopeProjection f hL d V c k)
      (fullEnvelopeProjection f hL d V c k) := by
  apply IsPullback.of_right _ (fullEnvelopeProjection_equalizes f hL d V c k)
    (fullEnvelope_isPullback f hL d V c k).flip
  rw [fullEnvelopeProjection_base]
  exact fullEnvelope_base_isPullback f hL d V c k

end FLT.Mazur.HilbertChart.AffineRestriction
