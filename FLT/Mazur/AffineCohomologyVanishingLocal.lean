/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CechAcyclicComparison
public import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# Local vanishing of positive sheaf cohomology classes

Every positive-degree class of the Ext cohomology presheaf vanishes near each
point. The proof shifts along an injective embedding. In degree one, local
surjectivity of its cokernel map lifts the section representing the class.
This is the local input to the cofinal-cover criterion for affine vanishing;
it does not assert global vanishing or require acyclic intersections.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace FLT.Mazur.AffineCohomologyVanishingLocal

open CechFreeOpen CechAcyclicComparison

variable {X : TopCat.{u}}
variable [HasExt.{u + 1}
  (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

local instance localVanishingHasExt : HasExt.{u + 1}
    (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstanceAs (HasExt.{u + 1}
    (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))

/-- Restriction in the cohomology presheaf is precomposition by the free-open map. -/
lemma restriction_eq (F : TopCat.Sheaf AddCommGrpCat.{u} X) {V W : Opens X}
    (i : V ⟶ W) (n : ℕ) (a : F.H' n W) :
    (F.cohomologyPresheaf n).map i.op a =
      (Abelian.Ext.mk₀ (freeOpenMap i)).comp a (zero_add n) := rfl

/-- Degree-zero evaluation commutes with restriction to a smaller open. -/
lemma hPrimeZeroEquiv_restrict (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    {V W : Opens X} (i : V ⟶ W) (a : F.H' 0 W) :
    hPrimeZeroEquiv V F ((F.cohomologyPresheaf 0).map i.op a) =
      F.obj.map i.op (hPrimeZeroEquiv W F a) := by
  obtain ⟨g, rfl⟩ := Abelian.Ext.addEquiv₀.symm.surjective a
  rw [restriction_eq]
  change freeOpenHomEquiv V F
    (Abelian.Ext.addEquiv₀ ((Abelian.Ext.mk₀ (freeOpenMap i)).comp
      (Abelian.Ext.mk₀ g) (zero_add 0))) = _
  rw [Abelian.Ext.mk₀_comp_mk₀]
  let eV : Abelian.Ext.{u + 1} (freeOpen V) F 0 ≃+ (freeOpen V ⟶ F) :=
    Abelian.Ext.addEquiv₀
  let eW : Abelian.Ext.{u + 1} (freeOpen W) F 0 ≃+ (freeOpen W ⟶ F) :=
    Abelian.Ext.addEquiv₀
  change freeOpenHomEquiv V F (eV (eV.symm (freeOpenMap i ≫ g))) =
    F.obj.map i.op (freeOpenHomEquiv W F (eW (eW.symm g)))
  rw [eV.apply_symm_apply, eW.apply_symm_apply]
  exact freeOpenHomEquiv_naturality_open i F g

/-- Every positive-degree Ext class vanishes on a neighborhood of each point. -/
lemma exists_neighborhood_zero (n : ℕ) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (W : Opens X) (a : F.H' (n + 1) W) (x : X) (hx : x ∈ W) :
    ∃ (V : Opens X) (i : V ⟶ W), x ∈ V ∧
      (F.cohomologyPresheaf (n + 1)).map i.op a = 0 := by
  induction n generalizing F W with
  | zero =>
    let S := embeddingSequence F
    have hS := embeddingSequence_shortExact F
    obtain ⟨b, hb⟩ := Abelian.Ext.covariant_sequence_exact₁ (freeOpen W) hS a
      (Abelian.Ext.eq_zero_of_injective _) (n₀ := 0) rfl
    have hg : TopCat.Presheaf.IsLocallySurjective S.g.hom :=
      (TopCat.Sheaf.isLocallySurjective_iff_epi S.g).mpr inferInstance
    obtain ⟨V, hV, ⟨t, ht⟩, hxV⟩ :=
      (TopCat.Presheaf.isLocallySurjective_iff S.g.hom).mp hg W
        (hPrimeZeroEquiv W S.X₃ b) x hx
    let i : V ⟶ W := homOfLE hV
    have hbV : (S.X₃.cohomologyPresheaf 0).map i.op b =
        ((hPrimeZeroEquiv V S.X₂).symm t).comp (Abelian.Ext.mk₀ S.g) (add_zero 0) := by
      apply (hPrimeZeroEquiv V S.X₃).injective
      rw [hPrimeZeroEquiv_restrict]
      change S.X₃.obj.map i.op (hPrimeZeroEquiv W S.X₃ b) =
        hPrimeZeroEquiv V S.X₃
          (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) 0).map
            S.g).app (op V) ((hPrimeZeroEquiv V S.X₂).symm t))
      rw [hPrimeZeroEquiv_naturality, AddEquiv.apply_symm_apply]
      exact ht.symm
    refine ⟨V, i, hxV, ?_⟩
    rw [restriction_eq, ← hb, ← Abelian.Ext.comp_assoc _ _ _ (zero_add 0) rfl
      (by omega)]
    change ((S.X₃.cohomologyPresheaf 0).map i.op b).comp hS.extClass rfl = 0
    rw [hbV, Abelian.Ext.comp_assoc_of_second_deg_zero,
      ShortComplex.ShortExact.comp_extClass, Abelian.Ext.comp_zero]
  | succ n ih =>
    let S := embeddingSequence F
    have hS := embeddingSequence_shortExact F
    obtain ⟨b, hb⟩ := Abelian.Ext.covariant_sequence_exact₁ (freeOpen W) hS a
      (Abelian.Ext.eq_zero_of_injective _) (n₀ := n + 1) rfl
    obtain ⟨V, i, hxV, hbV⟩ := ih S.X₃ W b hx
    refine ⟨V, i, hxV, ?_⟩
    rw [restriction_eq, ← hb, ← Abelian.Ext.comp_assoc _ _ _ (zero_add (n + 1)) rfl
      (by omega)]
    change ((S.X₃.cohomologyPresheaf (n + 1)).map i.op b).comp hS.extClass rfl = 0
    rw [hbV, Abelian.Ext.zero_comp]

open CechFreeResolution

/-- Global Ext cohomology is the cohomology presheaf evaluated on the whole space. -/
def sheafHTopEquiv (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    Sheaf.H F n ≃+ F.H' n ⊤ :=
  (((Abelian.extFunctor n).mapIso
    (asIso (freeOpenAugmentation (⊤ : Opens X))).op).app F).addCommGroupIsoToAddEquiv

/-- Restriction of a global Ext class to an open, using the free-open augmentation. -/
def restrictSheafH (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) (W : Opens X) :
    Sheaf.H F n →+ F.H' n W :=
  (Abelian.Ext.mk₀ (freeOpenAugmentation W)).precomp F (zero_add n)

/-- On the whole space, restriction is the canonical comparison isomorphism. -/
lemma restrictSheafH_top (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ)
    (a : Sheaf.H F n) : restrictSheafH F n ⊤ a = sheafHTopEquiv F n a := rfl

/-- Restrictions of global classes commute with open inclusions. -/
lemma restrictSheafH_naturality (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ)
    {V W : Opens X} (i : V ⟶ W) (a : Sheaf.H F n) :
    (F.cohomologyPresheaf n).map i.op (restrictSheafH F n W a) =
      restrictSheafH F n V a := by
  rw [restriction_eq]
  change (Abelian.Ext.mk₀ (freeOpenMap i)).comp
    ((Abelian.Ext.mk₀ (freeOpenAugmentation W)).comp a (zero_add n)) (zero_add n) = _
  rw [Abelian.Ext.mk₀_comp_mk₀_assoc, freeOpenMap_augmentation]
  rfl

/-- Every positive-degree global Ext class vanishes near every point. -/
lemma exists_neighborhood_restrictSheafH_zero (n : ℕ)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (a : Sheaf.H F (n + 1)) (x : X) :
    ∃ V : Opens X, x ∈ V ∧ restrictSheafH F (n + 1) V a = 0 := by
  obtain ⟨V, i, hxV, hV⟩ :=
    exists_neighborhood_zero n F ⊤ (restrictSheafH F (n + 1) ⊤ a) x trivial
  exact ⟨V, hxV, (restrictSheafH_naturality F (n + 1) i a).symm.trans hV⟩

end FLT.Mazur.AffineCohomologyVanishingLocal
