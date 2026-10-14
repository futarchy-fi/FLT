/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.MonomorphismFlatInverseImage
public import FLT.Mazur.KernelPairGenericEffectiveOpen
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Actual inverse neighborhoods in unramified candidate kernels

An etale original endpoint and an unramified candidate projection make the
full monomorphic relation comparison etale. Its image points therefore carry
actual scheme inverses; point coverage of the entire generic kernel now
suffices to construct a nonempty effective target, even when it is nonreduced.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.KernelPairEffectiveOpen
set_option backward.isDefEq.respectTransparency false
variable {D A T : Scheme} (p q : D ⟶ A) (w : A ⟶ T) (h : p ≫ w = q ≫ w)
  [Etale p] [LocallyOfFiniteType w] [FormallyUnramified w]
local notation "m" => pullback.lift p q h
local notation "b" => pullback.fst w w ≫ w

/-- Etaleness of the original endpoint constructs flatness of the full kernel comparison. -/
theorem comparison_etale_of_unramified : Etale m := by
  have he : Etale (m ≫ pullback.fst w w) := by
    rw [pullback.lift_fst]
    infer_instance
  let _ : FormallyUnramified (pullback.fst w w) :=
    MorphismProperty.pullback_fst w w inferInstance
  exact Etale.of_comp m (pullback.fst w w)

variable [Mono (pullback.lift p q h)]

/-- Every original relation image point has an actual inverse neighborhood in the full kernel. -/
theorem inverseLocus_eq_range_of_unramified :
    (MonomorphismOpenImage.locus m : Set (pullback w w : Scheme)) = Set.range m := by
  let _ := comparison_etale_of_unramified p q w h
  exact MonomorphismOpenImage.coe_locus_eq_range m

/-- Construct principal inverse charts around the entire original relation image. -/
theorem exists_principal_inverses_of_unramified
    [IsAffine (pullback w w)] [NoetherianSpace (pullback w w : Scheme)] :
    ∃ s : Finset Γ(pullback w w, ⊤),
      (∀ r ∈ s, ∃ a : ((pullback w w).basicOpen r).toScheme ⟶ D,
        a ≫ m = ((pullback w w).basicOpen r).ι) ∧
      ∀ x : (pullback w w : Scheme), x ∈ Set.range m ↔
        ∃ r ∈ s, x ∈ (pullback w w).basicOpen r := by
  let _ := comparison_etale_of_unramified p q w h
  exact MonomorphismOpenImage.exists_principal_inverse_cover_range m

/-- Generic point coverage now suffices: inverse morphisms are constructed, not assumed. -/
theorem targetOpen_nonempty_iff_generic_image [IsNoetherian A] [IsNoetherian T]
    [LocallyOfFinitePresentation w] [QuasiCompact w] [IrreducibleSpace T] :
    (targetOpen p q w h : Set T).Nonempty ↔
      ∀ x : (pullback w w : Scheme), b x = genericPoint T → x ∈ Set.range m := by
  rw [targetOpen_nonempty_iff_genericFiber]
  change (∀ x : (pullback w w : Scheme), b x = genericPoint T →
    x ∈ (MonomorphismOpenImage.locus m : Set (pullback w w : Scheme))) ↔ _
  rw [inverseLocus_eq_range_of_unramified p q w h]

end FLT.Mazur.KernelPairEffectiveOpen
