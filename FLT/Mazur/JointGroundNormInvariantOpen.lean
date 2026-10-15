/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.JointGroundNormInterior

/-!
# Full original invariance of joint norm domains

An original envelope section equation makes its full-fiber locus invariant.
Finite translation subcharts after ground change need not transport one by one:
their joint norm domain is nevertheless preserved by the full original relation.
This is invariance of the open, not an equality of the product coefficients.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeTranslationNorm
open Approximation SchemeOpenEnvelope HilbertChart.AffineRestriction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (V : Over (Spec (.of R)))
  {A D : Over (Spec (.of R))} (p q : D ⟶ A) (s : Γ((prod A V).left, ⊤))
  (hs : (prod.map p (𝟙 V)).left.appTop s = (prod.map q (𝟙 V)).left.appTop s)

include hs

/-- The section equation preserves all original fibers without any finite basis. -/
theorem fullFiberLocus_section_invariant :
    p.left ⁻¹' fullFiberLocus (prod.fst : prod A V ⟶ A).left
      ((prod A V).left.basicOpen s) =
    q.left ⁻¹' fullFiberLocus (prod.fst : prod A V ⟶ A).left
      ((prod A V).left.basicOpen s) := by
  have hp := ((IsPullback.of_prod_fst_with_id p V).map (Over.forget _)).flip
  have hq := ((IsPullback.of_prod_fst_with_id q V).map (Over.forget _)).flip
  refine (fullFiberLocus_baseChange hp ((prod A V).left.basicOpen s)).symm.trans
    (Eq.trans ?_ (fullFiberLocus_baseChange hq ((prod A V).left.basicOpen s)))
  change fullFiberLocus (prod.fst : prod D V ⟶ D).left
      ((prod.map p (𝟙 V)).left ⁻¹ᵁ (prod A V).left.basicOpen s) =
    fullFiberLocus (prod.fst : prod D V ⟶ D).left
      ((prod.map q (𝟙 V)).left ⁻¹ᵁ (prod A V).left.basicOpen s)
  rw [Scheme.preimage_basicOpen_top, Scheme.preimage_basicOpen_top, hs]

/-- Open original endpoints preserve the maximal original full-fiber neighborhood. -/
theorem fullFiberInterior_section_invariant (hp : IsOpenMap p.left) (hq : IsOpenMap q.left) :
    p.left ⁻¹ᵁ fullFiberInterior (prod.fst : prod A V ⟶ A).left
      ((prod A V).left.basicOpen s) =
    q.left ⁻¹ᵁ fullFiberInterior (prod.fst : prod A V ⟶ A).left
      ((prod A V).left.basicOpen s) :=
  fullFiberInterior_invariant _ _ p.left q.left hp hq
    (fullFiberLocus_section_invariant V p q s hs)

variable {S : Type} [CommRing S] (a : Spec (.of S) ⟶ Spec (.of R))
  (W : Over (Spec (.of S))) (w : (Over.map a).obj W ⟶ V)
  (H : IsPullback w.left W.hom V.hom a)
  {B : Over (Spec (.of S))} (u : (Over.map a).obj B ⟶ A)
  {I : Type} [Fintype I] (T : I → Over (Spec (.of S))) (t : ∀ i, T i ⟶ W)
  [∀ i, IsAffine (T i).left]
/-- The norms use the individual translation algebras. -/
local instance jointInvariantTranslationAlgebra (i : I) : Algebra S Γ((T i).left, ⊤) :=
  affineBaseSectionAlgebra (T i).hom
variable {ι : I → Type} [∀ i, Finite (ι i)]
  (b : ∀ i, Module.Basis (ι i) S Γ((T i).left, ⊤))
  (ht : ∀ z : W.left, ∃ i, ∃ y : (T i).left, (t i).left y = z)
local notation "n" => jointTranslationNorm B W T t b
  (Scheme.Hom.appTop (Over.Hom.left (fixedBaseEnvelopeMap a V W w u)) s)

include H ht

/-- Any actual original arrow preserves the product norm domain across independent new grounds. -/
theorem jointGroundNorm_open_transport {Z : Scheme} (x y : Z ⟶ B.left) (z : Z ⟶ D.left)
    (hx : z ≫ p.left = x ≫ u.left) (hy : z ≫ q.left = y ≫ u.left) :
    x ⁻¹ᵁ B.left.basicOpen n = y ⁻¹ᵁ B.left.basicOpen n := by
  apply SetLike.coe_injective
  change x ⁻¹' (B.left.basicOpen n : Set B.left) =
    y ⁻¹' (B.left.basicOpen n : Set B.left)
  rw [basicOpen_jointGroundNorm_fullFiber a V W w H u T t b ht s]
  have he := congrArg (fun C : Set D.left ↦ z ⁻¹' C)
    (fullFiberLocus_section_invariant V p q s hs)
  change (z ≫ p.left) ⁻¹' _ = (z ≫ q.left) ⁻¹' _ at he
  rw [hx, hy] at he
  exact he

end FLT.Mazur.SchemeTranslationNorm
