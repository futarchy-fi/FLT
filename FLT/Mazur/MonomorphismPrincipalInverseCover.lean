/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.MonomorphismOpenImage
public import FLT.Mazur.FinitePrincipalImageCover
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Finite principal inverse charts in the actual affine kernel

The entire inverse locus of a monomorphism into a Noetherian affine scheme
has a finite principal cover. Each chart has a constructed inverse into the
original relation, retaining the coefficient map and all nilpotents.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
namespace FLT.Mazur.MonomorphismOpenImage
variable {D K : Scheme.{u}} (m : D ⟶ K) [Mono m] [IsAffine K] [NoetherianSpace K]

/-- The actual inverse locus has finitely many principal charts with original-source inverses. -/
theorem exists_principal_inverse_cover :
    ∃ s : Finset Γ(K, ⊤), (⨆ r : s, K.basicOpen r.val) = locus m ∧
      ∀ r ∈ s, ∃ a : (K.basicOpen r).toScheme ⟶ D, a ≫ m = (K.basicOpen r).ι := by
  obtain ⟨s, hs, he⟩ := FinitePrincipalImageCover.exists_coefficients (locus m)
    (NoetherianSpace.isCompact _)
  refine ⟨s, he, fun r hr ↦ ⟨K.homOfLE (hs r hr) ≫ lift m, ?_⟩⟩
  rw [Category.assoc, lift_comp, Scheme.homOfLE_ι]

/-- Finitely many original principal inverse charts cover any prescribed good subset. -/
theorem subset_locus_iff_finite_principal (Z : Set K) : Z ⊆ locus m ↔
    ∃ s : Finset Γ(K, ⊤),
      (∀ r ∈ s, ∃ a : (K.basicOpen r).toScheme ⟶ D, a ≫ m = (K.basicOpen r).ι) ∧
      ∀ x ∈ Z, ∃ r ∈ s, x ∈ K.basicOpen r := by
  constructor
  · intro hZ
    obtain ⟨s, he, hs⟩ := exists_principal_inverse_cover m
    refine ⟨s, hs, fun x hx ↦ ?_⟩
    have hx' : x ∈ ⨆ r : s, K.basicOpen r.val := he.symm ▸ hZ hx
    obtain ⟨r, hr⟩ := Opens.mem_iSup.mp hx'
    exact ⟨r.val, r.property, hr⟩
  · rintro ⟨s, hs, hZ⟩ x hx
    obtain ⟨r, hr, hxr⟩ := hZ x hx
    obtain ⟨a, ha⟩ := hs r hr
    exact le_locus m (K.basicOpen r) a ha hxr

omit [IsAffine K] [NoetherianSpace K] in
/-- The principal inverses glue to the same original arrow on every scheme intersection. -/
theorem principal_inverses_agree (r s : Γ(K, ⊤))
    (a : (K.basicOpen r).toScheme ⟶ D) (b : (K.basicOpen s).toScheme ⟶ D)
    (ha : a ≫ m = (K.basicOpen r).ι) (hb : b ≫ m = (K.basicOpen s).ι) :
    Limits.pullback.fst (K.basicOpen r).ι (K.basicOpen s).ι ≫ a =
      Limits.pullback.snd (K.basicOpen r).ι (K.basicOpen s).ι ≫ b := by
  apply (cancel_mono m).mp
  rw [Category.assoc, Category.assoc, ha, hb]
  exact Limits.pullback.condition

end FLT.Mazur.MonomorphismOpenImage
