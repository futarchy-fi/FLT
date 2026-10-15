/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartesianEnvelopeSectionTransport
public import FLT.Mazur.SchemeRelationNormTransport

/-!
# Constructed norm compatibility on full Cartesian ground refinements

The translation may be finite free only over the new ground. Original
section compatibility still gives norm equality across all original arrows:
the envelopes and their section transports are constructed, not assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module
namespace FLT.Mazur.SchemeTranslationNorm
open Approximation HilbertChart.AffineRestriction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R S : Type} [CommRing R] [CommRing S]
  (a : Spec (.of S) ⟶ Spec (.of R))
  (V : Over (Spec (.of R))) (B W : Over (Spec (.of S)))
  (t : (Over.map a).obj W ⟶ V) (H : IsPullback t.left W.hom V.hom a)
  {A D : Over (Spec (.of R))} (u : (Over.map a).obj B ⟶ A)
  (p q : D ⟶ A) (s : Γ((prod A V).left, ⊤))
  (hs : (prod.map p (𝟙 V)).left.appTop s = (prod.map q (𝟙 V)).left.appTop s)
  [IsAffine W.left]
/-- Use the actual finite translation algebra over the new ground. -/
local instance cartesianNormTranslationAlgebra : Algebra S Γ(W.left, ⊤) :=
  affineBaseSectionAlgebra W.hom
variable {ι : Type} [Finite ι] (b : Basis ι S Γ(W.left, ⊤))
  {T : Scheme} (x y : T ⟶ B.left) (z : T ⟶ D.left)
  (hx : z ≫ p.left = x ≫ u.left) (hy : z ≫ q.left = y ≫ u.left)

include H hs hx hy in
/-- All original arrows preserve the norm of the pulled-back original envelope section. -/
theorem regularNorm_cartesianRelation :
    x.appTop (regularNorm B W b ((fixedBaseEnvelopeMap a V W t u).left.appTop s)) =
      y.appTop (regularNorm B W b ((fixedBaseEnvelopeMap a V W t u).left.appTop s)) := by
  apply regularNorm_eq_of_affineTransport B W B W b b _ _ x y T.affineCover
  intro i
  let j := T.affineCover.f i
  have hx' : (j ≫ z) ≫ p.left = (j ≫ x) ≫ u.left := by
    simpa only [Category.assoc] using congrArg (fun g ↦ j ≫ g) hx
  have hy' : (j ≫ z) ≫ q.left = (j ≫ y) ≫ u.left := by
    simpa only [Category.assoc] using congrArg (fun g ↦ j ≫ g) hy
  let h := originalRelation_ground_eq a B u p q (j ≫ x) (j ≫ y) (j ≫ z) hx' hy'
  refine ⟨cartesianGroundTransport a V B W t.left H (j ≫ x) (j ≫ y) h,
    cartesianGroundTransport_projection a V B W t.left H (j ≫ x) (j ≫ y) h, ?_⟩
  exact cartesianEnvelope_section_transport a V B W t H u p q
    (j ≫ x) (j ≫ y) (j ≫ z) hx' hy' s hs

include H hs hx hy in
/-- The precise nonvanishing open is preserved, without identifying new ground maps. -/
theorem basicOpen_regularNorm_cartesianRelation :
    x ⁻¹ᵁ B.left.basicOpen
        (regularNorm B W b ((fixedBaseEnvelopeMap a V W t u).left.appTop s)) =
      y ⁻¹ᵁ B.left.basicOpen
        (regularNorm B W b ((fixedBaseEnvelopeMap a V W t u).left.appTop s)) := by
  rw [Scheme.preimage_basicOpen_top, Scheme.preimage_basicOpen_top,
    regularNorm_cartesianRelation a V B W t H u p q s hs b x y z hx hy]

end FLT.Mazur.SchemeTranslationNorm
