/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperTranslationNeighborhoodInterior
public import FLT.Mazur.PartialGroundLocalInterior

/-!
# Original neighborhoods from constructed proper charts after ground change

The ambient Cartesian square retains original fullness. Proper neighborhoods
of the excluded changed translation coordinates construct the needed partial
charts, and one lift through an open source comparison suffices locally.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeTranslationNorm
open SchemeOpenEnvelope HilbertChart.AffineRestriction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R S : Type} [CommRing R] [CommRing S]
  (a : Spec (.of S) ⟶ Spec (.of R))
  (V : Over (Spec (.of R))) (W : Over (Spec (.of S)))
  (w : (Over.map a).obj W ⟶ V) (H : IsPullback w.left W.hom V.hom a)
  {A : Over (Spec (.of R))} {B : Over (Spec (.of S))}
  (u : (Over.map a).obj B ⟶ A) (U : (prod A V).left.Opens)
local notation "e" => Over.Hom.left (fixedBaseEnvelopeMap a V W w u)
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)
variable (hcompact : IsCompact
    ((fixedBaseEnvelopeMap a V W w u).left ⁻¹' (U : Set (prod A V).left))ᶜ)
  (hproper : ∀ y : (prod B W).left, (fixedBaseEnvelopeMap a V W w u).left y ∉ U →
    (prod.snd : prod B W ⟶ W).left y ∈ ProperNeighborhoodAtlas.locus W.hom)

include H hcompact hproper

/-- The canonical proper translation atlas makes the inverse image of original fullness open. -/
theorem isOpen_preimage_originalFullFiber_of_properNeighborhoods :
    IsOpen (u.left ⁻¹' fullFiberLocus π U) :=
  (congrArg IsOpen (fullFiberLocus_baseChange
    (fixedBaseEnvelopeMap_isPullback a V W w u H) U)).mp
      (isOpen_fullFiber_of_properTranslationNeighborhoods B W (e ⁻¹ᵁ U) hcompact hproper)

/-- A single original point lift through an open comparison constructs its original interior. -/
theorem mem_originalFullInterior_of_properNeighborhoods
    (hu : IsOpenMap u.left) (x : A.left)
    (hx : x ∈ fullFiberLocus π U) (hlift : x ∈ Set.range u.left) :
    x ∈ fullFiberInterior π U :=
  mem_fullFiberInterior_of_open_preimage π U u.left hu
    (isOpen_preimage_originalFullFiber_of_properNeighborhoods
      a V W w H u U hcompact hproper) x hx hlift

/-- Surjective open source comparisons descend the full-fiber open globally. -/
theorem isOpen_originalFullFiber_of_properNeighborhoods
    (hu : IsOpenMap u.left) (hsurj : Function.Surjective u.left) :
    IsOpen (fullFiberLocus π U) :=
  (hu.isQuotientMap u.left.continuous hsurj).isCoinducing.isOpen_preimage.mp
    (isOpen_preimage_originalFullFiber_of_properNeighborhoods
      a V W w H u U hcompact hproper)

/-- A finite set of reached original full fibers has one actual original source denominator. -/
theorem exists_originalDenominator_of_properNeighborhoods [IsAffine A.left]
    (hu : IsOpenMap u.left) (F : Set A.left) (hF : F.Finite)
    (hFU : F ⊆ fullFiberLocus π U) (hFlift : F ⊆ Set.range u.left) :
    ∃ r : Γ(A.left, ⊤), F ⊆ A.left.basicOpen r ∧ r ∈ denominatorIdeal (π).appTop.hom U := by
  apply exists_fullFiberInterior_coefficient π U F hF
  intro x hx
  exact mem_originalFullInterior_of_properNeighborhoods
    a V W w H u U hcompact hproper hu x (hFU hx) (hFlift hx)

omit hcompact in
/-- Affine changed envelopes supply the compactness required by this local construction. -/
theorem mem_originalFullInterior_of_affineProperNeighborhoods
    [IsAffine B.left] [IsAffine W.left] (hu : IsOpenMap u.left) (x : A.left)
    (hx : x ∈ fullFiberLocus π U) (hlift : x ∈ Set.range u.left) :
    x ∈ fullFiberInterior π U := by
  let _ : IsAffine (prod B W).left := IsAffine.of_isIso (Over.prodLeftIsoPullback B W).hom
  let _ : CompactSpace ((Over.map a).obj (prod B W)).left :=
    inferInstanceAs (CompactSpace (prod B W).left)
  exact mem_originalFullInterior_of_properNeighborhoods a V W w H u U
    (e ⁻¹ᵁ U).isOpen.isClosed_compl.isCompact hproper hu x hx hlift

end FLT.Mazur.SchemeTranslationNorm
