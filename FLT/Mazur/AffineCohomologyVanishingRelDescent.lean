/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineCohomologyVanishingCovers
public import FLT.Mazur.AffineCohomologyVanishingDescent

/-!
# Relative section descent

First Cech exactness corrects local lifts over any open into a compatible
family. On a principal open, local surjectivity supplies a finite principal
cover on which to apply this descent argument.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace FLT.Mazur.AffineCohomologyVanishingRelDescent

open CechSheafHZero AffineCohomologyVanishingDescent AffineCohomologyVanishingCovers

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

/-- Restrict a section on an open to a zero-cocycle on any family inside it. -/
def restrictZeroRelative (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (W : Opens X) (i : ∀ j, U j ⟶ W) :
    F.obj.obj (op W) →+ CechSheafH.zeroCocycles F U where
  toFun s := ⟨fun j ↦ F.obj.map (i j).op s, by
    rw [CechSheafH.mem_zeroCocycles_iff]
    intro j k
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl⟩
  map_zero' := by ext j; exact map_zero _
  map_add' s t := by ext j; exact map_add _ s t

/-- First Cech exactness glues local lifts over any open covered by the family. -/
lemma exists_section_lift_relative
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (W : Opens X) (hU : iSup U = W)
    (i : ∀ j, U j ⟶ W) (hF : (C U S.X₁).ExactAt 1)
    (s : S.X₃.obj.obj (op W)) (t : ∀ j, S.X₂.obj.obj (op (U j)))
    (ht : ∀ j, S.g.hom.app (op (U j)) (t j) = S.X₃.obj.map (i j).op s) :
    ∃ r : S.X₂.obj.obj (op W), S.g.hom.app (op W) r = s := by
  let z := (zeroTermEquiv U S.X₃).symm (restrictZeroRelative U S.X₃ W i s).val
  have hz : (C U S.X₃).d 0 1 z = 0 := by
    apply (coordinates_mem_iff U S.X₃ z).mp
    simpa only [z, AddEquiv.apply_symm_apply] using
      (restrictZeroRelative U S.X₃ W i s).property
  let y := (zeroTermEquiv U S.X₂).symm t
  have hy : termMap U S.g 0 y = z := by
    apply (zeroTermEquiv U S.X₃).injective
    funext j
    rw [zeroTermEquiv_naturality]
    change S.g.hom.app (op (U j))
      ((zeroTermEquiv U S.X₂) ((zeroTermEquiv U S.X₂).symm t) j) =
        ((zeroTermEquiv U S.X₃) ((zeroTermEquiv U S.X₃).symm _) j)
    rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    exact ht j
  obtain ⟨b, hb, hgb⟩ := lift_zero_cocycle U hS hF z hz y hy
  obtain ⟨r, hr, _⟩ := S.X₂.existsUnique_gluing' U W i (ge_of_eq hU)
    (zeroTermEquiv U S.X₂ b) ((d_zero_iff_compatible U S.X₂ b).mp hb)
  refine ⟨r, ?_⟩
  apply S.X₃.eq_of_locally_eq' U W i (ge_of_eq hU)
  intro j
  rw [← NatTrans.naturality_apply, hr j, ← zeroTermEquiv_naturality, hgb]
  exact congrFun ((zeroTermEquiv U S.X₃).apply_symm_apply _) j

variable {R : CommRingCat.{u}}

/-- Cech exactness on finite principal covers gives section surjectivity on a compact open. -/
lemma sections_surjective_on_compact
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of (Spec R)))}
    (hS : S.ShortExact) (W : Opens (PrimeSpectrum R))
    (hW : IsCompact (W : Set (PrimeSpectrum R)))
    (hC : ∀ s : Finset R, (⨆ f : s, PrimeSpectrum.basicOpen (f : R)) = W →
      (C (fun f : s ↦ PrimeSpectrum.basicOpen (f : R)) S.X₁).ExactAt 1) :
    Function.Surjective (S.g.hom.app (op W)) := by
  classical
  have := hS.epi_g
  intro a
  have hg : TopCat.Presheaf.IsLocallySurjective S.g.hom :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi S.g).mpr inferInstance
  let P (V : Opens (PrimeSpectrum R)) : Prop :=
    ∃ i : V ⟶ W, ∃ t, S.g.hom.app (op V) t = S.X₃.obj.map i.op a
  obtain ⟨s, hs, hlift⟩ := exists_finite_principal_cover W hW P
    (by
      rintro V V' hVV' ⟨i, t, ht⟩
      refine ⟨homOfLE hVV' ≫ i, S.X₂.obj.map (homOfLE hVV').op t, ?_⟩
      rw [NatTrans.naturality_apply, ht, op_comp, Functor.map_comp,
        ConcreteCategory.comp_apply])
    (by
      intro x hx
      obtain ⟨V, hV, ht, hxV⟩ :=
        (TopCat.Presheaf.isLocallySurjective_iff S.g.hom).mp hg W a x hx
      exact ⟨V, hxV, hV, homOfLE hV, ht⟩)
  have hlocal : ∀ f : s, ∃ i : PrimeSpectrum.basicOpen (f : R) ⟶ W,
      ∃ t, S.g.hom.app (op (PrimeSpectrum.basicOpen (f : R))) t =
        S.X₃.obj.map i.op a := fun f ↦ hlift f.val f.property
  choose i t ht using hlocal
  exact exists_section_lift_relative _ hS W hs i (hC s hs) a t ht

/-- The relative principal-cover criterion for quotient sections on a principal open. -/
lemma sections_surjective_on_basicOpen
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of (Spec R)))}
    (hS : S.ShortExact) (r : R)
    (hC : ∀ s : Finset R, (⨆ f : s, PrimeSpectrum.basicOpen (f : R)) =
        PrimeSpectrum.basicOpen r →
      (C (fun f : s ↦ PrimeSpectrum.basicOpen (f : R)) S.X₁).ExactAt 1) :
    Function.Surjective (S.g.hom.app (op (PrimeSpectrum.basicOpen r))) :=
  sections_surjective_on_compact hS _ (PrimeSpectrum.isCompact_basicOpen r) hC

end FLT.Mazur.AffineCohomologyVanishingRelDescent
