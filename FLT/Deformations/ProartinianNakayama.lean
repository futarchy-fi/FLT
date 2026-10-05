/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.ClosedIdealQuotient
public import Mathlib.RingTheory.Nakayama

/-!
# Nakayama for closed ideals of local proartinian rings

Apply ordinary Nakayama only in Artinian open quotients. Closedness then
recovers the conclusion in the original ring, without assuming that ring
is Noetherian or that its topology is adic.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace Deformation.ProartinianCat

variable {O : Type} [CommRing O] [IsLocalRing O] [Finite (ResidueField O)]
  (A : ProartinianCat O)

omit [IsLocalRing O] [Finite (ResidueField O)] in
/-- Membership in a closed ideal is detected in every proper open quotient. -/
theorem mem_closedIdeal_of_mem_sup_open (J : Ideal A) (hJ : IsClosed (J : Set A))
    {a : A} (ha : ∀ I : OpenIdeal A, a ∈ J ⊔ OpenIdeal.ideal I) : a ∈ J := by
  by_contra han
  have hU : (J : Set A)ᶜ ∈ nhds a := hJ.isOpen_compl.mem_nhds han
  have hV : (fun x : A ↦ a - x) ⁻¹' (J : Set A)ᶜ ∈ nhds (0 : A) := by
    have ht : ContinuousAt (fun x : A ↦ a - x) 0 :=
      (continuous_const.sub continuous_id).continuousAt
    exact ht.preimage_mem_nhds (by simpa using hU)
  obtain ⟨I, hI, hIV⟩ := IsLinearTopology.hasBasis_open_ideal.mem_iff.mp hV
  let K : OpenIdeal A := OrderDual.toDual ⟨I ⊓ maximalIdeal A,
    hI.inter isOpen_maximalIdeal_of_isProartinian,
    ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top inf_le_right⟩
  obtain ⟨j, hj, i, hi, hji⟩ := Submodule.mem_sup.mp (ha K)
  have hnot := hIV hi.1
  exact hnot (by simpa [← hji] using hj)

omit [IsLocalRing O] [Finite (ResidueField O)] in
/-- A closed ideal containing the maximal ideal modulo its square contains
it already. The finite generation used in Nakayama is only in finite quotients. -/
theorem maximalIdeal_le_of_le_sup_square (J : Ideal A) (hJ : IsClosed (J : Set A))
    (h : maximalIdeal A ≤ J ⊔ maximalIdeal A ^ 2) : maximalIdeal A ≤ J := by
  intro a ha
  apply mem_closedIdeal_of_mem_sup_open A J hJ
  intro I
  let Q := A ⧸ OpenIdeal.ideal I
  let f : A →+* Q := Ideal.Quotient.mk _
  let : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr (OpenIdeal.ne_top I)
  let : IsLocalRing Q := .of_surjective' f Ideal.Quotient.mk_surjective
  let : IsArtinianRing Q :=
    IsProartinian.isArtinianRing_quotient _ (OpenIdeal.isOpen I)
  have hm : (maximalIdeal A).map f = maximalIdeal Q :=
    map_maximalIdeal_of_surjective f Ideal.Quotient.mk_surjective
  have hq : maximalIdeal Q ≤ J.map f ⊔ maximalIdeal Q ^ 2 := by
    simpa only [Ideal.map_sup, Ideal.map_pow, hm] using Ideal.map_mono (f := f) h
  have hle : maximalIdeal Q ≤ J.map f :=
    Submodule.le_of_le_smul_of_le_jacobson_bot (maximalIdeal Q).fg_of_isNoetherianRing
      (by rw [jacobson_eq_maximalIdeal (⊥ : Ideal Q) bot_ne_top]) (by simpa [pow_two] using hq)
  have hx : f a ∈ J.map f := hle (hm ▸ Ideal.mem_map_of_mem f ha)
  have : a ∈ (J.map f).comap f := hx
  rw [Ideal.comap_map_of_surjective f Ideal.Quotient.mk_surjective] at this
  change a ∈ J ⊔ RingHom.ker (Ideal.Quotient.mk (OpenIdeal.ideal I)) at this
  simpa only [Ideal.mk_ker] using this

omit [IsLocalRing O] [Finite (ResidueField O)] in
/-- The hypothesis may use the topological closure of the square sum. -/
theorem maximalIdeal_le_of_le_closure_sup_square (J : Ideal A)
    (hJ : IsClosed (J : Set A))
    (h : maximalIdeal A ≤ (J ⊔ maximalIdeal A ^ 2).closure) : maximalIdeal A ≤ J := by
  intro a ha
  apply mem_closedIdeal_of_mem_sup_open A J hJ
  intro I
  let K := J ⊔ OpenIdeal.ideal I
  have hKopen : IsOpen (K : Set A) :=
    AddSubgroup.isOpen_mono (H₁ := (OpenIdeal.ideal I).toAddSubgroup)
      (H₂ := K.toAddSubgroup) (show OpenIdeal.ideal I ≤ K from le_sup_right) (OpenIdeal.isOpen I)
  have hKclosed : IsClosed (K : Set A) :=
    AddSubgroup.isClosed_of_isOpen K.toAddSubgroup hKopen
  have hSopen : IsOpen ((K ⊔ maximalIdeal A ^ 2 : Ideal A) : Set A) :=
    AddSubgroup.isOpen_mono (H₁ := K.toAddSubgroup)
      (H₂ := (K ⊔ maximalIdeal A ^ 2).toAddSubgroup)
      (show K ≤ K ⊔ maximalIdeal A ^ 2 from le_sup_left) hKopen
  have hSclosed : IsClosed ((K ⊔ maximalIdeal A ^ 2 : Ideal A) : Set A) :=
    AddSubgroup.isClosed_of_isOpen (K ⊔ maximalIdeal A ^ 2).toAddSubgroup hSopen
  exact maximalIdeal_le_of_le_sup_square A K hKclosed
    (h.trans (closure_minimal
      (show J ⊔ maximalIdeal A ^ 2 ≤ K ⊔ maximalIdeal A ^ 2 from
        sup_le_sup_right le_sup_left _) hSclosed)) ha

/-- A finite generating family modulo the closed square sum generates the
actual maximal ideal; compactness supplies closedness of its span. -/
theorem maximalIdeal_eq_of_fg_of_le_closure_sup_square (J : Ideal A) (hfg : J.FG)
    (hJ : J ≤ maximalIdeal A)
    (h : maximalIdeal A ≤ (J ⊔ maximalIdeal A ^ 2).closure) : maximalIdeal A = J :=
  le_antisymm (maximalIdeal_le_of_le_closure_sup_square A J
    (Ideal.isCompact_of_fg hfg).isClosed h) hJ

end Deformation.ProartinianCat
