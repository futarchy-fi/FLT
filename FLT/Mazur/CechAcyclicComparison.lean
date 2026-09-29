/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CechDimensionShift
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Topology.Sheaves.Abelian

/-!
# Comparison for an acyclic cover

The degree-zero comparison descends to cokernels in degree one. Higher degrees
are defined by dimension shifting along a chosen injective embedding. Acyclicity
of each successive cokernel follows from the Ext long exact sequence.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace FLT.Mazur.CechAcyclicComparison

open CechSheafHZero CechAcyclicCokernel CechDimensionShift CechConnecting

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X) (hU : iSup U = ⊤)
variable [HasExt.{u + 1}
  (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

local instance comparisonHasExt : HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstanceAs (HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))

/-- The comparison in degree zero, oriented from Cech to Ext. -/
def zeroComparison (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    CH U F 0 ≃+ Sheaf.H F 0 := (sheafHZeroEquiv U hU F).symm

/-- The degree-zero comparison commutes with coefficient maps. -/
lemma zeroComparison_naturality {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) (x : CH U F 0) :
    zeroComparison U hU G (CHmap U f 0 x) =
      Sheaf.H.map f 0 (zeroComparison U hU F x) := by
  apply (sheafHZeroEquiv U hU G).injective
  simpa only [zeroComparison, AddEquiv.apply_symm_apply] using
    (sheafHZeroEquiv_naturality U hU f ((sheafHZeroEquiv U hU F).symm x)).symm

/-- The degree-zero comparison identifies the images of a coefficient map. -/
lemma zeroComparison_range {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) :
    (CHmap U f 0).hom.range.map (zeroComparison U hU G).toAddMonoidHom =
      (Sheaf.H.map f 0).range := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨zeroComparison U hU F x, (zeroComparison_naturality U hU f x).symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨CHmap U f 0 ((zeroComparison U hU F).symm x), ⟨_, rfl⟩, ?_⟩
    change zeroComparison U hU G (CHmap U f 0 _) = _
    rw [zeroComparison_naturality, AddEquiv.apply_symm_apply]

/-- The quotient comparison used in first cohomology. -/
def zeroQuotientComparison {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) :
    (CH U G 0 ⧸ (CHmap U f 0).hom.range) ≃+
      (Sheaf.H G 0 ⧸ (Sheaf.H.map f 0).range) :=
  QuotientAddGroup.congr _ _ (zeroComparison U hU G) (zeroComparison_range U hU f)

@[simp]
lemma zeroQuotientComparison_mk {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) (x : CH U G 0) :
    zeroQuotientComparison U hU f (QuotientAddGroup.mk x) =
      QuotientAddGroup.mk (zeroComparison U hU G x) := rfl

/-- First cohomology compared using any injective middle term. -/
def oneComparison {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) [Injective S.X₂] (hF : CoverAcyclic U S.X₁) :
    CH U S.X₁ 1 ≃+ Sheaf.H S.X₁ 1 :=
  (cechOneEquiv U hU hS hF).symm.trans
    ((zeroQuotientComparison U hU S.g).trans (sheafOneEquiv hS))

/-- On a connecting class the comparison is induced by degree zero. -/
lemma oneComparison_delta {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) [Injective S.X₂] (hF : CoverAcyclic U S.X₁)
    (x : CH U S.X₃ 0) :
    oneComparison U hU hS hF (cechDelta U hS hF 0 x) =
      Sheaf.H.δ hS 0 1 rfl (zeroComparison U hU S.X₃ x) := by
  change ((zeroQuotientComparison U hU S.g).trans (sheafOneEquiv hS))
    ((cechOneEquiv U hU hS hF).symm
      (cechOneEquiv U hU hS hF (QuotientAddGroup.mk x))) = _
  rw [AddEquiv.symm_apply_apply]
  rfl

omit [HasExt.{u + 1}
  (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] in
/-- A sheaf embedded in its chosen injective, followed by the cokernel. -/
abbrev embeddingSequence (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)

omit [HasExt.{u + 1}
  (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] in
/-- The chosen embedding and its cokernel form a short exact sequence. -/
lemma embeddingSequence_shortExact (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (embeddingSequence F).ShortExact :=
  { exact := ShortComplex.exact_cokernel (Injective.ι F) }

/-- Cokernel acyclicity is derived at each step of the recursion. -/
lemma embeddingSequence_acyclic (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hF : CoverAcyclic U F) : CoverAcyclic U (embeddingSequence F).X₃ :=
  coverAcyclic_cokernel U (embeddingSequence_shortExact F) hF

local instance comparisonEnoughInjectives :
    EnoughInjectives (TopCat.Sheaf AddCommGrpCat.{u} X) := inferInstance

/-- The comparison in degree one for the chosen embedding. -/
def chosenOneComparison (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hF : CoverAcyclic U F) : CH U F 1 ≃+ Sheaf.H F 1 :=
  oneComparison U hU (S := embeddingSequence F) (embeddingSequence_shortExact F) hF

/-- Transport a comparison through the chosen dimension shifts. -/
def nextComparison (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hF : CoverAcyclic U F) (n : ℕ)
    (e : CH U (embeddingSequence F).X₃ (n + 1) ≃+
      Sheaf.H (embeddingSequence F).X₃ (n + 1)) :
    CH U F (n + 2) ≃+ Sheaf.H F (n + 2) :=
  (cechShiftEquiv U hU (S := embeddingSequence F)
    (embeddingSequence_shortExact F) hF n).symm.trans
      (e.trans (sheafShiftEquiv (embeddingSequence_shortExact F) n))

/-- Cech cohomology of an acyclic cover equals Ext-based sheaf cohomology. -/
def acyclicCoverEquiv (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hF : CoverAcyclic U F) : (n : ℕ) → CH U F n ≃+ Sheaf.H F n
  | 0 => zeroComparison U hU F
  | 1 => chosenOneComparison U hU F hF
  | n + 2 => nextComparison U hU F hF n
      (acyclicCoverEquiv (embeddingSequence F).X₃
        (embeddingSequence_acyclic U F hF) (n + 1))

@[simp]
lemma acyclicCoverEquiv_zero (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hF : CoverAcyclic U F) : acyclicCoverEquiv U hU F hF 0 = zeroComparison U hU F := rfl

/-- The defining compatibility with the first connecting map. -/
lemma acyclicCoverEquiv_one_delta (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hF : CoverAcyclic U F) (x : CH U (embeddingSequence F).X₃ 0) :
    acyclicCoverEquiv U hU F hF 1
      (cechDelta U (embeddingSequence_shortExact F) hF 0 x) =
      Sheaf.H.δ (embeddingSequence_shortExact F) 0 1 rfl
        (zeroComparison U hU (embeddingSequence F).X₃ x) :=
  oneComparison_delta U hU (embeddingSequence_shortExact F) hF x

/-- The defining compatibility with the higher connecting maps. -/
lemma acyclicCoverEquiv_succ_delta (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hF : CoverAcyclic U F) (n : ℕ) (x : CH U (embeddingSequence F).X₃ (n + 1)) :
    acyclicCoverEquiv U hU F hF (n + 2)
      (cechDelta U (embeddingSequence_shortExact F) hF (n + 1) x) =
      Sheaf.H.δ (embeddingSequence_shortExact F) (n + 1) (n + 2) rfl
        (acyclicCoverEquiv U hU (embeddingSequence F).X₃
          (embeddingSequence_acyclic U F hF) (n + 1) x) := by
  change sheafShiftEquiv (embeddingSequence_shortExact F) n
    (acyclicCoverEquiv U hU (embeddingSequence F).X₃
      (embeddingSequence_acyclic U F hF) (n + 1)
      ((cechShiftEquiv U hU (embeddingSequence_shortExact F) hF n).symm
        (cechShiftEquiv U hU (embeddingSequence_shortExact F) hF n x))) = _
  rw [AddEquiv.symm_apply_apply]
  rfl

/-- The comparison commutes with every connecting map in the chosen sequence. -/
lemma acyclicCoverEquiv_chosen_delta (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hF : CoverAcyclic U F) (n : ℕ) (x : CH U (embeddingSequence F).X₃ n) :
    acyclicCoverEquiv U hU F hF (n + 1)
      (cechDelta U (embeddingSequence_shortExact F) hF n x) =
      Sheaf.H.δ (embeddingSequence_shortExact F) n (n + 1) rfl
        (acyclicCoverEquiv U hU (embeddingSequence F).X₃
          (embeddingSequence_acyclic U F hF) n x) := by
  cases n with
  | zero => exact acyclicCoverEquiv_one_delta U hU F hF x
  | succ n => exact acyclicCoverEquiv_succ_delta U hU F hF n x

end FLT.Mazur.CechAcyclicComparison
