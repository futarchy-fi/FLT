/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CechAcyclicComparison

/-!
# Naturality and independence of the acyclic-cover comparison

Coefficient maps extend to injective embeddings. Naturality of the connecting
maps then proves naturality of the comparison by induction. Exactness identifies
the difference between two lifts as a boundary. Finally the comparison can be
computed using any injective embedding, independently of the chosen one.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace FLT.Mazur.CechAcyclicNaturality

open CechSheafHZero CechAcyclicCokernel CechDimensionShift CechConnecting
open CechAcyclicComparison CechInjectiveAcyclic

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X) (hU : iSup U = ⊤)
variable [HasExt.{u + 1}
  (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

local instance naturalityHasExt : HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstanceAs (HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))

omit [HasExt.{u + 1}
  (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] in
/-- Extend a coefficient map through an injective middle term and descend to cokernels. -/
def extendCoefficient {S T : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) [Injective T.X₂] (f : S.X₁ ⟶ T.X₁) : S ⟶ T := by
  have := hS.mono_f
  have := hS.epi_g
  let l := Injective.factorThru (f ≫ T.f) S.f
  have hl : S.f ≫ l = f ≫ T.f := Injective.comp_factorThru _ _
  have hz : S.f ≫ (l ≫ T.g) = 0 := by
    rw [← Category.assoc, hl, Category.assoc, T.zero, comp_zero]
  exact
    { τ₁ := f
      τ₂ := l
      τ₃ := hS.exact.desc (l ≫ T.g) hz
      comm₁₂ := hl.symm
      comm₂₃ := (hS.exact.g_desc _ hz).symm }

omit [HasExt.{u + 1}
  (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] in
@[simp]
lemma extendCoefficient_τ₁ {S T : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) [Injective T.X₂] (f : S.X₁ ⟶ T.X₁) :
    (extendCoefficient hS f).τ₁ = f := rfl

/-- The acyclic-cover comparison is natural in every coefficient morphism. -/
lemma acyclicCoverEquiv_naturality {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (hF : CoverAcyclic U F) (hG : CoverAcyclic U G) (f : F ⟶ G)
    (n : ℕ) (x : CH U F n) :
    acyclicCoverEquiv U hU G hG n (CHmap U f n x) =
      Sheaf.H.map f n (acyclicCoverEquiv U hU F hF n x) := by
  induction n generalizing F G with
  | zero => exact zeroComparison_naturality U hU f x
  | succ n ih =>
    let φ : embeddingSequence F ⟶ embeddingSequence G :=
      extendCoefficient (embeddingSequence_shortExact F) f
    obtain ⟨y, rfl⟩ := cechDelta_surjective U hU (embeddingSequence_shortExact F) hF n x
    change acyclicCoverEquiv U hU G hG (n + 1)
      (CHmap U φ.τ₁ (n + 1) (cechDelta U (embeddingSequence_shortExact F) hF n y)) = _
    rw [cechDelta_naturality_apply U (embeddingSequence_shortExact F) hF
      (embeddingSequence_shortExact G) hG φ n y,
      acyclicCoverEquiv_chosen_delta, acyclicCoverEquiv_chosen_delta, ih]
    exact Sheaf.H.δ_naturality n (n + 1) rfl
      (embeddingSequence_shortExact F) (embeddingSequence_shortExact G) φ _

omit [HasExt.{u + 1}
  (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] in
/-- The identity coefficient map acts identically on Cech cohomology. -/
lemma chMap_id_apply (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) (x : CH U F n) :
    CHmap U (𝟙 F) n x = x := by
  change HomologicalComplex.homologyMap ((cechComplexFunctor U).map (𝟙 F.obj)) n x = x
  simp

variable {S T : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}

/-- Two extensions of the same coefficient map differ by a boundary on the cokernel. -/
lemma lift_difference_boundary (hS : S.ShortExact) (hF : CoverAcyclic U S.X₁)
    (hT : T.ShortExact) (hG : CoverAcyclic U T.X₁)
    (φ ψ : S ⟶ T) (h : φ.τ₁ = ψ.τ₁) (n : ℕ) (x : CH U S.X₃ n) :
    ∃ y : CH U T.X₂ n, CHmap U T.g n y = CHmap U φ.τ₃ n x - CHmap U ψ.τ₃ n x := by
  apply (cechDelta_exact U hT hG n _).mp
  rw [map_sub, ← cechDelta_naturality_apply U hS hF hT hG φ,
    ← cechDelta_naturality_apply U hS hF hT hG ψ, h, sub_self]

include hU in
/-- In positive degrees the cokernel map itself is independent of the extension. -/
lemma lift_independent_positive (hS : S.ShortExact) (hF : CoverAcyclic U S.X₁)
    (hT : T.ShortExact) [Injective T.X₂] (hG : CoverAcyclic U T.X₁)
    (φ ψ : S ⟶ T) (h : φ.τ₁ = ψ.τ₁) (n : ℕ) (x : CH U S.X₃ (n + 1)) :
    CHmap U φ.τ₃ (n + 1) x = CHmap U ψ.τ₃ (n + 1) x := by
  obtain ⟨y, hy⟩ := lift_difference_boundary U hS hF hT hG φ ψ h (n + 1) x
  have := AddCommGrpCat.subsingleton_of_isZero (cech_isZero_of_injective U hU T.X₂ n)
  rw [Subsingleton.elim y 0, map_zero] at hy
  exact sub_eq_zero.mp hy.symm

/-- In degree zero the induced class modulo the preceding range is independent of the lift. -/
lemma lift_independent_zero (hS : S.ShortExact) (hF : CoverAcyclic U S.X₁)
    (hT : T.ShortExact) (hG : CoverAcyclic U T.X₁)
    (φ ψ : S ⟶ T) (h : φ.τ₁ = ψ.τ₁) (x : CH U S.X₃ 0) :
    (QuotientAddGroup.mk (CHmap U φ.τ₃ 0 x) :
      CH U T.X₃ 0 ⧸ (CHmap U T.g 0).hom.range) =
      QuotientAddGroup.mk (CHmap U ψ.τ₃ 0 x) := by
  obtain ⟨y, hy⟩ := lift_difference_boundary U hS hF hT hG φ ψ h 0 x
  exact QuotientAddGroup.eq_iff_sub_mem.mpr ⟨y, hy⟩

/-- The comparison commutes with dimension shifting along any injective embedding. -/
lemma acyclicCoverEquiv_delta (hS : S.ShortExact) [Injective S.X₂]
    (hF : CoverAcyclic U S.X₁) (n : ℕ) (x : CH U S.X₃ n) :
    acyclicCoverEquiv U hU S.X₁ hF (n + 1) (cechDelta U hS hF n x) =
      Sheaf.H.δ hS n (n + 1) rfl
        (acyclicCoverEquiv U hU S.X₃ (coverAcyclic_cokernel U hS hF) n x) := by
  let φ : S ⟶ embeddingSequence S.X₁ := extendCoefficient hS (𝟙 S.X₁)
  have hc : cechDelta U hS hF n x =
      cechDelta U (embeddingSequence_shortExact S.X₁) hF n (CHmap U φ.τ₃ n x) := by
    simpa only [show φ.τ₁ = 𝟙 S.X₁ from rfl, chMap_id_apply] using
      cechDelta_naturality_apply U hS hF (embeddingSequence_shortExact S.X₁) hF φ n x
  rw [hc, acyclicCoverEquiv_chosen_delta,
    acyclicCoverEquiv_naturality U hU (coverAcyclic_cokernel U hS hF)
      (embeddingSequence_acyclic U S.X₁ hF) φ.τ₃ n x]
  exact (Sheaf.H.δ_naturality n (n + 1) rfl hS (embeddingSequence_shortExact S.X₁) φ
    (acyclicCoverEquiv U hU S.X₃ (coverAcyclic_cokernel U hS hF) n x)).trans
      (Sheaf.H.map_id_apply _)

/-- Compute positive-degree comparison using any injective middle term. -/
def comparisonFromSequence (hS : S.ShortExact) [Injective S.X₂]
    (hF : CoverAcyclic U S.X₁) : (n : ℕ) → CH U S.X₁ (n + 1) ≃+ Sheaf.H S.X₁ (n + 1)
  | 0 => oneComparison U hU hS hF
  | n + 1 => (cechShiftEquiv U hU hS hF n).symm.trans
      ((acyclicCoverEquiv U hU S.X₃ (coverAcyclic_cokernel U hS hF) (n + 1)).trans
        (sheafShiftEquiv hS n))

/-- The computation from an arbitrary sequence has the same connecting-map formula. -/
lemma comparisonFromSequence_delta (hS : S.ShortExact) [Injective S.X₂]
    (hF : CoverAcyclic U S.X₁) (n : ℕ) (x : CH U S.X₃ n) :
    comparisonFromSequence U hU hS hF n (cechDelta U hS hF n x) =
      Sheaf.H.δ hS n (n + 1) rfl
        (acyclicCoverEquiv U hU S.X₃ (coverAcyclic_cokernel U hS hF) n x) := by
  cases n with
  | zero => exact oneComparison_delta U hU hS hF x
  | succ n =>
    change sheafShiftEquiv hS n
      (acyclicCoverEquiv U hU S.X₃ (coverAcyclic_cokernel U hS hF) (n + 1)
        ((cechShiftEquiv U hU hS hF n).symm (cechShiftEquiv U hU hS hF n x))) = _
    rw [AddEquiv.symm_apply_apply]
    rfl

/-- Any injective embedding computes the same additive equivalence. -/
lemma comparisonFromSequence_eq (hS : S.ShortExact) [Injective S.X₂]
    (hF : CoverAcyclic U S.X₁) (n : ℕ) :
    comparisonFromSequence U hU hS hF n = acyclicCoverEquiv U hU S.X₁ hF (n + 1) := by
  ext x
  obtain ⟨y, rfl⟩ := cechDelta_surjective U hU hS hF n x
  rw [comparisonFromSequence_delta, acyclicCoverEquiv_delta]

end FLT.Mazur.CechAcyclicNaturality
