/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Exact products of disjoint closed equation ideals

Disjoint closed subschemes of an affine test have comaximal scalar ideals.
For a finite family their intersection is their product, exactly rather than
only after taking radicals. Empty families are included.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped BigOperators
namespace FLT.Mazur.SchemeDisjointClosedIdeals
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y T : Scheme.{0}} [IsAffine T] (f : X ⟶ T) (g : Y ⟶ T)
  [IsClosedImmersion f] [IsClosedImmersion g]

/-- Disjoint full closed equations have comaximal exact scalar kernels. -/
theorem kernels_coprime (h : Disjoint (Set.range f) (Set.range g)) :
    IsCoprime (RingHom.ker f.appTop.hom) (RingHom.ker g.appTop.hom) := by
  have hs : f.ker ⊔ g.ker = ⊤ := by
    apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
    rw [Scheme.IdealSheafData.support_sup]
    apply SetLike.coe_injective
    change (f.ker.support : Set T) ∩ g.ker.support = ∅
    rw [Scheme.Hom.support_ker, Scheme.Hom.support_ker,
      (IsClosedImmersion.isClosedEmbedding f).isClosed_range.closure_eq,
      (IsClosedImmersion.isClosedEmbedding g).isClosed_range.closure_eq]
    exact Set.disjoint_iff_inter_eq_empty.mp h
  rw [Ideal.isCoprime_iff_sup_eq]
  have he := congrArg (fun K : T.IdealSheafData ↦ K.ideal ⟨⊤, isAffineOpen_top T⟩) hs
  simpa only [Scheme.IdealSheafData.ideal_sup, Pi.sup_apply,
    Scheme.IdealSheafData.ideal_top, Pi.top_apply, Scheme.Hom.ker_apply] using he

/-- A finite disjoint family has an exact product formula for its full scalar kernel. -/
theorem iInf_kernel_eq_prod {I : Type} [Fintype I] {Z : I → Scheme.{0}}
    (j : ∀ i, Z i ⟶ T) [∀ i, IsClosedImmersion (j i)]
    (hj : Pairwise fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))) :
    (⨅ i, RingHom.ker (j i).appTop.hom) = ∏ i, RingHom.ker (j i).appTop.hom := by
  classical
  symm
  simpa using Ideal.prod_eq_iInf_of_pairwise_isCoprime
    (s := Finset.univ) (J := fun i ↦ RingHom.ker (j i).appTop.hom)
    (fun i _ k _ hik ↦ kernels_coprime (j i) (j k) (hj hik))

end FLT.Mazur.SchemeDisjointClosedIdeals
