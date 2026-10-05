/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.ProartinianQuotients
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.RingTheory.Finiteness.Ideal

/-!
# The adic topology from finite generation of the maximal ideal

Compactness makes finitely generated ideals closed. Finite residue field
then makes every maximal-ideal power open, giving the topology comparison
without a Noetherian hypothesis.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace Deformation.ProartinianCat

variable {O : Type} [CommRing O] [IsLocalRing O] [Finite (ResidueField O)]
  (A : ProartinianCat O)

/-- A finitely generated maximal ideal has open powers in the original topology. -/
theorem maximalIdeal_pow_isOpen_of_fg (hfg : (maximalIdeal A).FG) (n : ℕ) :
    IsOpen ((maximalIdeal A ^ n : Ideal A) : Set A) := by
  let : Finite (A ⧸ maximalIdeal A) :=
    AddSubgroup.quotient_finite_of_isOpen _ isOpen_maximalIdeal_of_isProartinian
  let : Finite (A ⧸ maximalIdeal A ^ n) := Ideal.finite_quotient_pow hfg n
  have hclosed : IsClosed ((maximalIdeal A ^ n : Ideal A) : Set A) :=
    (Ideal.isCompact_of_fg hfg.pow).isClosed
  let : Finite (A ⧸ (maximalIdeal A ^ n).toAddSubgroup) :=
    inferInstanceAs (Finite (A ⧸ maximalIdeal A ^ n))
  let : (maximalIdeal A ^ n).toAddSubgroup.FiniteIndex :=
    AddSubgroup.finiteIndex_of_finite_quotient
  exact AddSubgroup.isOpen_of_isClosed_of_finiteIndex
    (maximalIdeal A ^ n).toAddSubgroup hclosed

/-- Finite generation, rather than Noetherianity, suffices for the adic topology. -/
theorem isAdicTopology_of_maximalIdeal_fg (hfg : (maximalIdeal A).FG) :
    IsAdicTopology A := by
  refine ⟨isAdic_iff.mpr ⟨maximalIdeal_pow_isOpen_of_fg A hfg, ?_⟩⟩
  intro s hs
  obtain ⟨I, hI, hIs⟩ := IsLinearTopology.hasBasis_open_ideal.mem_iff.mp hs
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_le_of_isProartinian I hI
  exact ⟨n, Set.Subset.trans hn hIs⟩

/-- Separation for the maximal-ideal filtration follows from the original
Hausdorff topology and the topology comparison. -/
theorem isHausdorff_maximalIdeal_of_fg (hfg : (maximalIdeal A).FG) :
    IsHausdorff (maximalIdeal A) A := by
  let := isAdicTopology_of_maximalIdeal_fg A hfg
  constructor
  intro a ha
  by_contra hne
  have hU : ({a}ᶜ : Set A) ∈ nhds (0 : A) :=
    isOpen_compl_singleton.mem_nhds (by simpa using Ne.symm hne)
  obtain ⟨n, _, hn⟩ := (hasBasis_maximalIdeal_pow A).mem_iff.mp hU
  have hm : a ∈ maximalIdeal A ^ n := by
    simpa [SModEq.zero, ← Ideal.one_eq_top, smul_eq_mul] using ha n
  exact hn hm (by simp)

/-- A finitely generated maximal ideal makes the original compact ring adically complete. -/
theorem isAdicComplete_of_maximalIdeal_fg (hfg : (maximalIdeal A).FG) :
    IsAdicComplete (maximalIdeal A) A := by
  let := isAdicTopology_of_maximalIdeal_fg A hfg
  let := isHausdorff_maximalIdeal_of_fg A hfg
  exact ⟨⟩

end Deformation.ProartinianCat
