/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.JointTranslationNormSupport

/-!
# Original full-fiber interiors from joint norms after ground change

Only the ambient translation is a full Cartesian base change. Its finite free
cover members may be proper subcharts. Their norm product detects the entire
original fiber, and an open surjective source comparison descends its openness.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeTranslationNorm
open Approximation SchemeOpenEnvelope HilbertChart.AffineRestriction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R S : Type} [CommRing R] [CommRing S]
  (a : Spec (.of S) ⟶ Spec (.of R))
  (V : Over (Spec (.of R))) (W : Over (Spec (.of S)))
  (w : (Over.map a).obj W ⟶ V) (H : IsPullback w.left W.hom V.hom a)
  {A : Over (Spec (.of R))} {B : Over (Spec (.of S))} (u : (Over.map a).obj B ⟶ A)
  {I : Type} [Fintype I] (T : I → Over (Spec (.of S))) (t : ∀ i, T i ⟶ W)
  [∀ i, IsAffine (T i).left]
/-- The norm algebras are those of the individual changed-ground translations. -/
local instance jointGroundTranslationAlgebra (i : I) : Algebra S Γ((T i).left, ⊤) :=
  affineBaseSectionAlgebra (T i).hom
variable {ι : I → Type} [∀ i, Finite (ι i)]
  (b : ∀ i, Module.Basis (ι i) S Γ((T i).left, ⊤))
  (ht : ∀ z : W.left, ∃ i, ∃ y : (T i).left, (t i).left y = z)
  (s : Γ((prod A V).left, ⊤))
local notation "n" => jointTranslationNorm B W T t b
  (Scheme.Hom.appTop (Over.Hom.left (fixedBaseEnvelopeMap a V W w u)) s)
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)
local notation "U" => Scheme.basicOpen (Over.left (prod A V)) s

include H ht b

/-- All finite chart norms together retain every original residue-field branch. -/
theorem basicOpen_jointGroundNorm_fullFiber :
    (B.left.basicOpen n : Set B.left) = u.left ⁻¹' fullFiberLocus π U := by
  refine Eq.trans ?_
    (fullFiberLocus_baseChange (fixedBaseEnvelopeMap_isPullback a V W w u H) U)
  rw [Scheme.preimage_basicOpen_top]
  exact basicOpen_jointTranslationNorm_fullFiber B W T t b _ ht

/-- Open source comparison identifies the product domain with the original full interior. -/
theorem basicOpen_jointGroundNorm_fullInterior (hu : IsOpenMap u.left) :
    B.left.basicOpen n = u.left ⁻¹ᵁ fullFiberInterior π U := by
  apply SetLike.coe_injective
  change _ = u.left ⁻¹' interior (fullFiberLocus π U)
  rw [hu.preimage_interior_eq_interior_preimage u.left.continuous,
    ← basicOpen_jointGroundNorm_fullFiber a V W w H u T t b ht s]
  exact (B.left.basicOpen _).isOpen.interior_eq.symm

omit [Fintype I] in
/-- The original full-fiber locus is open by descent along an open surjective source map. -/
theorem isOpen_originalFullFiber_of_jointGroundCover [Finite I] (hu : IsOpenMap u.left)
    (hsurj : Function.Surjective u.left) : IsOpen (fullFiberLocus π U) := by
  let _ := Fintype.ofFinite I
  apply (hu.isQuotientMap u.left.continuous hsurj).isCoinducing.isOpen_preimage.mp
  rw [← basicOpen_jointGroundNorm_fullFiber a V W w H u T t b ht s]
  exact (B.left.basicOpen _).isOpen

omit [Fintype I] in
/-- Every original full-fiber point then lies in an actual open full-fiber neighborhood. -/
theorem originalFullInterior_eq_fullFiber_of_jointGroundCover [Finite I] (hu : IsOpenMap u.left)
    (hsurj : Function.Surjective u.left) :
    (fullFiberInterior π U : Set A.left) = fullFiberLocus π U :=
  (isOpen_originalFullFiber_of_jointGroundCover a V W w H u T t b ht s hu hsurj).interior_eq

/-- The original full-fiber open is the image of the constructed changed-ground norm open. -/
theorem originalFullInterior_image_jointGroundNorm (hu : IsOpenMap u.left)
    (hsurj : Function.Surjective u.left) :
    u.left '' (B.left.basicOpen n : Set B.left) = fullFiberInterior π U := by
  rw [basicOpen_jointGroundNorm_fullInterior a V W w H u T t b ht s hu]
  change u.left '' (u.left ⁻¹' (fullFiberInterior π U : Set A.left)) = _
  exact Set.image_preimage_eq _ hsurj

end FLT.Mazur.SchemeTranslationNorm
