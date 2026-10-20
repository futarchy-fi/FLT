/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Finite families factor locally through covering open sections

An open section cover of a scheme gives simultaneous local factorizations
of finitely many test maps. The equalities are equalities of scheme maps
over the original base, including its nilpotent structure.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.OpenSectionFamilyLocalFactorization
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u v w
variable {X S T : Scheme.{u}} (p : X ⟶ S) {L : Type v}
  (s : L → (S ⟶ X)) [∀ a, IsOpenImmersion (s a)]
  (hs : ∀ a, s a ≫ p = 𝟙 S)

include hs

/-- Landing in an open section determines the complete factorization over the base. -/
theorem factor_of_range_subset (q : T ⟶ X) (f : T ⟶ S) (hq : q ≫ p = f)
    (a : L) (ha : Set.range q ⊆ Set.range (s a)) : q = f ≫ s a := by
  let k := IsOpenImmersion.lift (s a) q ha
  have hk : k ≫ s a = q := IsOpenImmersion.lift_fac _ _ _
  have he : k = f := by
    have h := congrArg (fun z => z ≫ p) hk
    simpa only [Category.assoc, hs, Category.comp_id, hq] using h
  exact hk.symm.trans (congrArg (fun z => z ≫ s a) he)

/-- A finite family of maps acquires actual labels on one affine neighborhood of each point. -/
theorem exists_affine_family {J : Type w} [Finite J]
    (hcover : ∀ z : X, ∃ (a : L) (y : S), s a y = z)
    (q : J → (T ⟶ X)) (f : T ⟶ S) (hq : ∀ j, q j ≫ p = f) (x : T) :
    ∃ (a : J → L) (U : T.Opens), IsAffineOpen U ∧ x ∈ U ∧
      ∀ j, U.ι ≫ q j = (U.ι ≫ f) ≫ s (a j) := by
  classical
  choose a y hy using fun j => hcover (q j x)
  let O : T.Opens := ⨅ j, q j ⁻¹ᵁ (s (a j)).opensRange
  have hx : x ∈ O := by
    change x ∈ (O : Set T)
    simp only [O, Opens.coe_iInf]
    exact Set.mem_iInter.mpr (fun j => ⟨y j, hy j⟩)
  obtain ⟨U, hU, hxU, hUO⟩ := exists_isAffineOpen_mem_and_subset hx
  refine ⟨a, U, hU, hxU, fun j => ?_⟩
  apply factor_of_range_subset p s hs (U.ι ≫ q j) (U.ι ≫ f)
    (by rw [Category.assoc, hq])
  rintro _ ⟨z, rfl⟩
  have hz : z.val ∈ (O : Set T) := hUO z.property
  simp only [O, Opens.coe_iInf] at hz
  exact Set.mem_iInter.mp hz j

end FLT.Mazur.OpenSectionFamilyLocalFactorization
