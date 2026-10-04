/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.ClosedIdealQuotient
public import FLT.Deformations.RepresentationTheory.FlatIntersection

/-!
# An effective ideal for finite-flat open reductions

Intersect all open coefficient ideals whose reductions have finite-flat
models. Compactness and intersection stability prove that an open reduction
is finite flat exactly when its ideal contains this closed ideal.
-/

@[expose] public noncomputable section
open NumberField
namespace Deformation
open ProartinianCat
variable {O : Type} [CommRing O] [IsLocalRing O]
  [Finite (IsLocalRing.ResidueField O)] (U : ProartinianCat O)
  {K : Type} [Field K] [NumberField K] {n : Type} [Finite n]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (ρ : FramedGaloisRep K U n)

/-- Open coefficient ideals admitting the actual finite-flat model predicate. -/
def flatReductionIdeals : Set (Ideal U) :=
  {I | IsOpen (I : Set U) ∧ (GaloisRep.baseChange (U ⧸ I) ρ).HasFlatProlongationAt v}

/-- The closed ideal imposed by all finite-flat open reductions. -/
def flatReductionIdeal : Ideal U := sInf (flatReductionIdeals U v ρ)

omit [IsLocalRing O] [Finite (IsLocalRing.ResidueField O)] in
/-- Open additive subgroups are closed, so this intersection is closed. -/
theorem flatReductionIdeal_closed : IsClosed (flatReductionIdeal U v ρ : Set U) := by
  change IsClosed (⋂ I ∈ flatReductionIdeals U v ρ, (I : Set U))
  exact isClosed_biInter fun I hI ↦ I.toAddSubgroup.isClosed_of_isOpen hI.1

omit [IsLocalRing O] [Finite (IsLocalRing.ResidueField O)] in
/-- Any one finite-flat reduction contains the defining ideal. -/
theorem flatReductionIdeal_le {I : Ideal U} (hI : I ∈ flatReductionIdeals U v ρ) :
    flatReductionIdeal U v ρ ≤ I := sInf_le hI

omit [IsLocalRing O] [Finite (IsLocalRing.ResidueField O)] in
/-- Two admissible open ideals have an admissible intersection. -/
theorem flatReductionIdeals_inf {I J : Ideal U}
    (hI : I ∈ flatReductionIdeals U v ρ) (hJ : J ∈ flatReductionIdeals U v ρ) :
    I ⊓ J ∈ flatReductionIdeals U v ρ :=
  ⟨hI.1.inter hJ.1, GaloisRep.hasFlatProlongationAt_quotient_inf v ρ hI.2 hJ.2⟩

/-- Compactness makes the finite-flat reductions cofinal above their intersection. -/
theorem flatReductionIdeal_cofinal
    (hex : (flatReductionIdeals U v ρ).Nonempty) {J : Ideal U}
    (hJ : IsOpen (J : Set U)) (hle : flatReductionIdeal U v ρ ≤ J) :
    ∃ I ∈ flatReductionIdeals U v ρ, I ≤ J := by
  let T := {I : Ideal U // I ∈ flatReductionIdeals U v ρ}
  have : Nonempty T := ⟨⟨hex.choose, hex.choose_spec⟩⟩
  have hi : (⋂ I : T, (I.val : Set U)) ⊆ (J : Set U) := by
    intro x hx
    apply hle
    change x ∈ sInf (flatReductionIdeals U v ρ)
    rw [Ideal.mem_sInf]
    intro I hI
    exact Set.mem_iInter.mp hx ⟨I, hI⟩
  obtain ⟨I, hI⟩ := hJ.isClosed_compl.isCompact.elim_directed_family_closed
    (fun I : T ↦ (I.val : Set U))
    (fun I ↦ I.val.toAddSubgroup.isClosed_of_isOpen I.property.1)
    (Set.disjoint_left.mpr fun x hx hxi ↦ hx (hi hxi)) (by
      intro I L
      exact ⟨⟨I.val ⊓ L.val, flatReductionIdeals_inf U v ρ I.property L.property⟩,
        inf_le_left, inf_le_right⟩)
  refine ⟨I.val, I.property, ?_⟩
  intro x hx
  by_contra h
  exact Set.disjoint_left.mp hI h hx

/-- The closed condition is effective for every open coefficient reduction. -/
theorem flatReductionIdeal_le_iff
    (hex : (flatReductionIdeals U v ρ).Nonempty) {J : Ideal U}
    (hJ : IsOpen (J : Set U)) :
    flatReductionIdeal U v ρ ≤ J ↔
      (GaloisRep.baseChange (U ⧸ J) ρ).HasFlatProlongationAt v := by
  constructor
  · intro h
    obtain ⟨I, hI, hIJ⟩ := flatReductionIdeal_cofinal U v ρ hex hJ h
    exact GaloisRep.hasFlatProlongationAt_quotient_of_le v ρ hIJ hI.2
  · exact fun h ↦ flatReductionIdeal_le U v ρ ⟨hJ, h⟩

omit [IsLocalRing O] [Finite (IsLocalRing.ResidueField O)] in
/-- A proper residual finite-flat reduction proves properness of the closed ideal. -/
theorem flatReductionIdeal_ne_top {I : Ideal U}
    (hI : I ∈ flatReductionIdeals U v ρ) (hne : I ≠ ⊤) :
    flatReductionIdeal U v ρ ≠ ⊤ :=
  ne_top_of_le_ne_top hne (flatReductionIdeal_le U v ρ hI)

end Deformation
