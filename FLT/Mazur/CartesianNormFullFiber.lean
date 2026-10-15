/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertCartesianEnvelope
public import FLT.Mazur.SchemeTranslationNormFiber
public import FLT.Mazur.SchemeOpenEnvelopeInterior

/-!
# Cartesian norms retain the entire original full-fiber domain

A full translation base change preserves the full-fiber locus of an actual
original envelope section. If the source comparison is open, its norm open
is precisely the inverse image of the original full-fiber interior. No
original finite basis or global extension of the chosen section is needed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeOpenEnvelope
universe u
variable {E F X Y : Scheme.{u}} {g : E ⟶ F} {p : E ⟶ X} {q : F ⟶ Y} {v : X ⟶ Y}
  (H : IsPullback g p q v) (U : F.Opens)

include H

/-- A Cartesian square tests all points in the original fiber, including residue extensions. -/
theorem fullFiberLocus_baseChange :
    fullFiberLocus p (g ⁻¹ᵁ U) = v ⁻¹' fullFiberLocus q U := by
  ext x
  rw [Set.mem_preimage, mem_fullFiberLocus, mem_fullFiberLocus]
  constructor
  · intro h z hz
    obtain ⟨e, he, hx⟩ := Scheme.exists_preimage_of_isPullback H z x hz
    have hu := h e hx
    change g e ∈ U at hu
    rwa [he] at hu
  · intro h e he
    apply h
    have hw := congrArg (fun f : E ⟶ Y ↦ f e) H.w
    exact hw.trans (congrArg v he)

/-- Open source changes preserve the actual maximal open full-fiber domain. -/
theorem fullFiberInterior_baseChange (hv : IsOpenMap v) :
    fullFiberInterior p (g ⁻¹ᵁ U) = v ⁻¹ᵁ fullFiberInterior q U := by
  apply SetLike.coe_injective
  change interior (fullFiberLocus p (g ⁻¹ᵁ U)) = v ⁻¹' interior (fullFiberLocus q U)
  rw [fullFiberLocus_baseChange H U, hv.preimage_interior_eq_interior_preimage v.continuous]

end FLT.Mazur.SchemeOpenEnvelope

namespace FLT.Mazur.SchemeTranslationNorm
open Approximation HilbertChart.AffineRestriction SchemeOpenEnvelope
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R S : Type} [CommRing R] [CommRing S]
  (a : Spec (.of S) ⟶ Spec (.of R))
  (V : Over (Spec (.of R))) (W : Over (Spec (.of S)))
  (t : (Over.map a).obj W ⟶ V) (H : IsPullback t.left W.hom V.hom a)
  {A : Over (Spec (.of R))} {B : Over (Spec (.of S))}
  (v : (Over.map a).obj B ⟶ A) [IsAffine W.left]
/-- The finite basis is needed only over the changed ground. -/
local instance cartesianFiberTranslationAlgebra : Algebra S Γ(W.left, ⊤) :=
  affineBaseSectionAlgebra W.hom
variable {ι : Type} [Finite ι] (b : Module.Basis ι S Γ(W.left, ⊤))
  (s : Γ((prod A V).left, ⊤))

include H

/-- The norm is nonzero exactly above the original entire-fiber nonvanishing locus. -/
theorem basicOpen_cartesianNorm_fullFiber :
    (B.left.basicOpen (regularNorm B W b
      ((fixedBaseEnvelopeMap a V W t v).left.appTop s)) : Set B.left) =
      v.left ⁻¹' fullFiberLocus (prod.fst : prod A V ⟶ A).left
        ((prod A V).left.basicOpen s) := by
  refine Eq.trans ?_ (fullFiberLocus_baseChange
    (fixedBaseEnvelopeMap_isPullback a V W t v H) ((prod A V).left.basicOpen s))
  rw [Scheme.preimage_basicOpen_top]
  ext x
  exact (mem_basicOpen_regularNorm_iff B W b _ x).trans (mem_fullFiberLocus _ _ x).symm

/-- An open source comparison identifies the norm open with the original full-fiber interior. -/
theorem basicOpen_cartesianNorm_fullInterior (hv : IsOpenMap v.left) :
    B.left.basicOpen (regularNorm B W b
      ((fixedBaseEnvelopeMap a V W t v).left.appTop s)) =
      v.left ⁻¹ᵁ fullFiberInterior (prod.fst : prod A V ⟶ A).left
        ((prod A V).left.basicOpen s) := by
  apply SetLike.coe_injective
  change _ = v.left ⁻¹' interior (fullFiberLocus _ _)
  rw [hv.preimage_interior_eq_interior_preimage v.left.continuous,
    ← basicOpen_cartesianNorm_fullFiber a V W t H v b s]
  exact (B.left.basicOpen _).isOpen.interior_eq.symm

end FLT.Mazur.SchemeTranslationNorm
