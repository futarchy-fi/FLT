/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CechConnecting
public import FLT.Mazur.CechInjectiveAcyclic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Dimension shifting for Cech and sheaf cohomology

For a short exact coefficient sequence with injective middle term, the connecting
maps are isomorphisms in positive degrees. In degree zero they instead identify
the cokernel of the map on sections with first cohomology. The Cech statements
require a covering family and acyclicity on its finite intersections.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace FLT.Mazur.CechDimensionShift

open CechSheafHZero CechAcyclicCokernel CechConnecting CechInjectiveAcyclic

/-- A surjective map in an exact pair identifies the quotient by the preceding range. -/
def quotientRangeEquiv {A B D : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup D] (f : A →+ B) (g : B →+ D) (h : Function.Exact f g)
    (hg : Function.Surjective g) : (B ⧸ f.range) ≃+ D :=
  (QuotientAddGroup.quotientAddEquivOfEq (AddMonoidHom.exact_iff.mp h).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective g hg)

@[simp]
lemma quotientRangeEquiv_mk {A B D : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup D] (f : A →+ B) (g : B →+ D) (h : Function.Exact f g)
    (hg : Function.Surjective g) (x : B) :
    quotientRangeEquiv f g h hg (QuotientAddGroup.mk x) = g x := rfl

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X) (hU : iSup U = ⊤)
variable [HasExt.{u + 1}
  (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

local instance cechDimensionShiftInst1 : HasExt.{u + 1}
    (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstanceAs (HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))

variable {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
  (hS : S.ShortExact) [Injective S.X₂] (hF : CoverAcyclic U S.X₁)

include hU in
/-- Vanishing in the middle makes the Cech connecting map surjective. -/
lemma cechDelta_surjective (n : ℕ) : Function.Surjective (cechDelta U hS hF n) := by
  have := AddCommGrpCat.subsingleton_of_isZero (cech_isZero_of_injective U hU S.X₂ n)
  intro x
  exact (cechDelta_exact_next U hS hF n x).mp (Subsingleton.elim _ 0)

include hU in
/-- In positive degree the Cech connecting map is also injective. -/
lemma cechDelta_injective (n : ℕ) : Function.Injective (cechDelta U hS hF (n + 1)) := by
  have := AddCommGrpCat.subsingleton_of_isZero (cech_isZero_of_injective U hU S.X₂ n)
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨y, hy⟩ := (cechDelta_exact U hS hF (n + 1) x).mp hx
  rw [Subsingleton.elim y 0, map_zero] at hy
  exact hy.symm

/-- Positive Cech cohomology shifts along the connecting map. -/
def cechShiftEquiv (n : ℕ) : CH U S.X₃ (n + 1) ≃+ CH U S.X₁ (n + 2) :=
  AddEquiv.ofBijective (cechDelta U hS hF (n + 1))
    ⟨cechDelta_injective U hU hS hF n, cechDelta_surjective U hU hS hF (n + 1)⟩

@[simp]
lemma cechShiftEquiv_apply (n : ℕ) (x : CH U S.X₃ (n + 1)) :
    cechShiftEquiv U hU hS hF n x = cechDelta U hS hF (n + 1) x := rfl

/-- First Cech cohomology is the cokernel of the degree-zero coefficient map. -/
def cechOneEquiv :
    (CH U S.X₃ 0 ⧸ (CHmap U S.g 0).hom.range) ≃+ CH U S.X₁ 1 :=
  quotientRangeEquiv (CHmap U S.g 0).hom (cechDelta U hS hF 0)
    (cechDelta_exact U hS hF 0) (cechDelta_surjective U hU hS hF 0)

@[simp]
lemma cechOneEquiv_mk (x : CH U S.X₃ 0) :
    cechOneEquiv U hU hS hF (QuotientAddGroup.mk x) = cechDelta U hS hF 0 x := rfl

variable {T : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
  (hT : T.ShortExact) [Injective T.X₂] (hG : CoverAcyclic U T.X₁)

/-- Cech dimension shifting is natural in short exact coefficient sequences. -/
lemma cechShiftEquiv_naturality (φ : ShortComplex.Hom S T) (n : ℕ)
    (x : CH U S.X₃ (n + 1)) :
    CHmap U φ.τ₁ (n + 2) (cechShiftEquiv U hU hS hF n x) =
      cechShiftEquiv U hU hT hG n (CHmap U φ.τ₃ (n + 1) x) :=
  cechDelta_naturality_apply U hS hF hT hG φ (n + 1) x

/-- Vanishing of positive Ext into an injective makes the connecting map surjective. -/
lemma sheafDelta_surjective (n : ℕ) :
    Function.Surjective (Sheaf.H.δ hS n (n + 1) rfl) := by
  intro x
  exact Sheaf.H.longSequence_exact₁ hS x (Subsingleton.elim _ 0) rfl

/-- In positive degree the Ext connecting map is injective. -/
lemma sheafDelta_injective (n : ℕ) :
    Function.Injective (Sheaf.H.δ hS (n + 1) (n + 2) rfl) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨y, hy⟩ := Sheaf.H.longSequence_exact₃ hS x rfl hx
  rw [Subsingleton.elim y 0, map_zero] at hy
  exact hy.symm

/-- Positive Ext-based sheaf cohomology shifts along its connecting map. -/
def sheafShiftEquiv (n : ℕ) : Sheaf.H S.X₃ (n + 1) ≃+ Sheaf.H S.X₁ (n + 2) :=
  AddEquiv.ofBijective (Sheaf.H.δ hS (n + 1) (n + 2) rfl)
    ⟨sheafDelta_injective hS n, sheafDelta_surjective hS (n + 1)⟩

@[simp]
lemma sheafShiftEquiv_apply (n : ℕ) (x : Sheaf.H S.X₃ (n + 1)) :
    sheafShiftEquiv hS n x = Sheaf.H.δ hS (n + 1) (n + 2) rfl x := rfl

/-- Ext dimension shifting is natural in short exact coefficient sequences. -/
lemma sheafShiftEquiv_naturality (φ : ShortComplex.Hom S T) (n : ℕ)
    (x : Sheaf.H S.X₃ (n + 1)) :
    Sheaf.H.map φ.τ₁ (n + 2) (sheafShiftEquiv hS n x) =
      sheafShiftEquiv hT n (Sheaf.H.map φ.τ₃ (n + 1) x) :=
  (Sheaf.H.δ_naturality (n + 1) (n + 2) rfl hS hT φ x).symm

/-- First sheaf cohomology is the cokernel of the map on degree-zero Ext. -/
def sheafOneEquiv :
    (Sheaf.H S.X₃ 0 ⧸ (Sheaf.H.map S.g 0).range) ≃+ Sheaf.H S.X₁ 1 :=
  quotientRangeEquiv (Sheaf.H.map S.g 0) (Sheaf.H.δ hS 0 1 rfl)
    ((ShortComplex.ab_exact_iff_function_exact _).mp
      (Sheaf.H.longSequence_exact₃' hS 0 1 rfl)) (sheafDelta_surjective hS 0)

@[simp]
lemma sheafOneEquiv_mk (x : Sheaf.H S.X₃ 0) :
    sheafOneEquiv hS (QuotientAddGroup.mk x) = Sheaf.H.δ hS 0 1 rfl x := rfl

end FLT.Mazur.CechDimensionShift
