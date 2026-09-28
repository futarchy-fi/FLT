/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CechAcyclicCokernel
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Connecting maps in Cech cohomology

When the first sheaf in a short exact sequence is acyclic on cover intersections,
the associated Cech complexes form a short exact sequence. Its homology sequence
provides connecting maps, exactness, and naturality in the coefficient sequence.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace FLT.Mazur.CechConnecting

open CechSheafHZero CechAcyclicCokernel

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

/-- The Cech complex functor on sheaves. -/
abbrev sheafCechFunctor :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ CochainComplex AddCommGrpCat.{u} ℕ :=
  sheafToPresheaf _ _ ⋙ cechComplexFunctor U

instance cechConnectingInst1 : (sheafCechFunctor U).PreservesZeroMorphisms where
  map_zero F G := by
    ext n x
    apply (termEquiv U G n).injective
    funext a
    change termEquiv U G n (((cechComplexFunctor U).map (0 : F ⟶ G).hom).f n x) a =
      termEquiv U G n 0 a
    rw [termEquiv_naturality]
    simp

/-- The short complex of Cech complexes induced by a coefficient sequence. -/
abbrev cechShortComplex (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)) :=
  S.map (sheafCechFunctor U)

variable [HasExt.{u + 1}
  (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
variable {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
  (hS : S.ShortExact) (hF : CoverAcyclic U S.X₁)

include hS hF in
/-- Acyclicity of the first sheaf makes the Cech coefficient sequence short exact. -/
lemma cechShortComplex_shortExact : (cechShortComplex U S).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact cech_degree_shortExact U hS hF n

/-- The connecting homomorphism in Cech cohomology. -/
def cechDelta (n : ℕ) : CH U S.X₃ n →+ CH U S.X₁ (n + 1) :=
  ((cechShortComplex_shortExact U hS hF).δ n (n + 1) rfl).hom

/-- Exactness at the cohomology of the quotient sheaf. -/
lemma cechDelta_exact (n : ℕ) :
    Function.Exact (CHmap U S.g n) (cechDelta U hS hF n) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    ((cechShortComplex_shortExact U hS hF).homology_exact₃ n (n + 1) rfl)

/-- Exactness at the next cohomology of the first sheaf. -/
lemma cechDelta_exact_next (n : ℕ) :
    Function.Exact (cechDelta U hS hF n) (CHmap U S.f (n + 1)) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    ((cechShortComplex_shortExact U hS hF).homology_exact₁ n (n + 1) rfl)

variable {T : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
  (hT : T.ShortExact) (hG : CoverAcyclic U T.X₁)

/-- Connecting maps commute with morphisms of short exact coefficient sequences. -/
lemma cechDelta_naturality (φ : ShortComplex.Hom S T) (n : ℕ) :
    (CHmap U φ.τ₁ (n + 1)).hom.comp (cechDelta U hS hF n) =
      (cechDelta U hT hG n).comp (CHmap U φ.τ₃ n).hom := by
  exact congrArg (fun f ↦ f.hom) (HomologicalComplex.HomologySequence.δ_naturality
    ((sheafCechFunctor U).mapShortComplex.map φ)
    (cechShortComplex_shortExact U hS hF)
    (cechShortComplex_shortExact U hT hG) n (n + 1) rfl)

/-- Pointwise naturality of the Cech connecting homomorphism. -/
lemma cechDelta_naturality_apply (φ : ShortComplex.Hom S T) (n : ℕ)
    (x : CH U S.X₃ n) :
    CHmap U φ.τ₁ (n + 1) (cechDelta U hS hF n x) =
      cechDelta U hT hG n (CHmap U φ.τ₃ n x) :=
  DFunLike.congr_fun (cechDelta_naturality U hS hF hT hG φ n) x

end FLT.Mazur.CechConnecting
