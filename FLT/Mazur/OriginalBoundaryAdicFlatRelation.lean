/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryFlatRelationLift
public import FLT.Mazur.SchemeGenerizingVanishingNeighborhood

/-!
# Original lifts from actual adic discrepancies on a flat scalar branch

A quasi-compact flat scalar branch has a Noetherian full arrow pullback.
All-order membership of the actual pulled-back discrepancy, supported over
all generizations of the branch point, constructs a branch neighborhood and
then an original principal lift. Neither scalar map is required to be closed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open SchemeEffectiveEpiSections SchemeScalarPrincipalNeighborhood
open SchemeAdicVanishingNeighborhood InvariantOpenCoefficientRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A Y : Scheme.{0}} {p q : D ⟶ A} [IsNoetherian D] [IsAffine A]
local notation "σD" => p.appTop.hom.comp (Subring.subtype (compatibleFunctions p q))
variable (g : Y ⟶ Spec (.of (compatibleFunctions p q)))
  [Flat g] [LocallyOfFinitePresentation g] [QuasiCompact g]
local notation "π" => scalarMorphism σD
local notation "k" => pullback.fst π g
local notation "h" => pullback.snd π g
local notation "Z" => (pullback π g : Scheme)
variable (J : A.IdealSheafData) (t : Γ(J.subscheme, ⊤))
  (a : Γ(A, ⊤)) (ha : J.subschemeι.appTop a = t)

include ha in
/-- Full generizing branch germs construct original lifts without either scalar map being closed. -/
theorem exists_principalBoundaryLift_of_flat_generizing_germs
    (y : Y) (hy : ∀ z : Z, h z ⤳ y →
      (Z).presheaf.germ ⊤ z (by trivial)
        ((k).appTop (p.appTop a - q.appTop a)) = 0) :
    ∃ (s : compatibleFunctions p q), s ∉ (g y).asIdeal ∧
      ∃ u : coefficients p q (A.basicOpen s.val) (compatibleFunctions_basicOpen p q s),
        (J.comap (A.basicOpen s.val).ι).subschemeι.appTop u.val =
          (IdealSheafClosedTransitions.map (J.comap (A.basicOpen s.val).ι) J
            (A.basicOpen s.val).ι rfl).appTop t := by
  let _ : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian k
  let _ := QuasiCompact.compactSpace_of_compactSpace k
  let _ : IsNoetherian Z := ⟨⟩
  obtain ⟨V, hyV, hV⟩ := exists_target_neighborhood_of_generizing_germs h _ y hy
  exact exists_principalBoundaryLift_of_flat_relation_branch g V J t a ha y hyV hV

include ha in
/-- All-order errors of one actual original section suffice on the whole generizing branch fiber. -/
theorem exists_principalBoundaryLift_of_adic_flat_generizations
    (I : (Z).IdealSheafData)
    (hadic : ∀ (U : (Z).affineOpens) (n : ℕ),
      (Z).presheaf.map (homOfLE le_top : U.1 ⟶ ⊤).op
        ((k).appTop (p.appTop a - q.appTop a)) ∈ I.ideal U ^ (n + 1))
    (y : Y) (hy : ∀ z : Z, h z ⤳ y → z ∈ I.support) :
    ∃ (s : compatibleFunctions p q), s ∉ (g y).asIdeal ∧
      ∃ u : coefficients p q (A.basicOpen s.val) (compatibleFunctions_basicOpen p q s),
        (J.comap (A.basicOpen s.val).ι).subschemeι.appTop u.val =
          (IdealSheafClosedTransitions.map (J.comap (A.basicOpen s.val).ι) J
            (A.basicOpen s.val).ι rfl).appTop t := by
  let _ : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian k
  apply exists_principalBoundaryLift_of_flat_generizing_germs g J t a ha y
  intro z hz
  exact germ_eq_zero_of_adic _ I hadic z (hy z hz)

end FLT.Mazur.EquivalenceRelationOrderedFrames
