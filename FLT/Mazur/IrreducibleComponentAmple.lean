/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteSurjectiveAmpleDescent

/-!
# Ampleness on reduced irreducible components

Every irreducible closed subset lies in an irreducible component. Its reduced
closed immersion factors through that component, so affine pullback transfers
ampleness. Geometric ideal filtration and finite direct-image vanishing then
give the ampleness criterion on a scheme proper over a Noetherian ring.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace ZeroObject
open Scheme.Modules FLT.Mazur.CoherentIdealIntersection

namespace FLT.Mazur.FCurve
open CoherentDevissage

variable {R : Type} [CommRing R] [IsNoetherianRing R] {X : Scheme}
  (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] {L : X.Modules}

/-- Reduced closed inclusions transport ampleness from a larger closed subset. -/
theorem ample_reducedClosed_of_le (Z W : Closeds X) (hZW : Z ≤ W)
    (hW : AmpleLineBundle ((pullback (reducedClosedSubschemeι W)).obj L)) :
    AmpleLineBundle ((pullback (reducedClosedSubschemeι Z)).obj L) := by
  let h := Scheme.IdealSheafData.vanishingIdeal_antimono hZW
  let a := Scheme.IdealSheafData.inclusion h
  have ha := hW.pullback_affine a
  apply ha.of_iso
  exact (pullbackCongr (Scheme.IdealSheafData.inclusion_subschemeι h).symm).app L ≪≫
    ((pullbackComp a (reducedClosedSubschemeι W)).app L).symm

include f in
/-- Ample restrictions to all integral closed subsets give vanishing for every coherent sheaf. -/
theorem eventualTwistVanishing_of_integral_restrictions (hL : LocallyFreeRankOne L)
    (hclosed : ∀ Z : Closeds X, IsIrreducible (Z : Set X) →
      AmpleLineBundle ((pullback (reducedClosedSubschemeι Z)).obj L))
    (M : X.Modules) [M.IsFinitePresentation] : EventualTwistVanishing L M := by
  have := Chow.source_isNoetherian f
  apply geometric_ideal_criterion
    (fun h p₁ p₃ ↦ EventualTwistVanishing.middle hL _ h.shortExact p₁ p₃)
    (EventualTwistVanishing.of_isZero L 0 (Limits.isZero_zero _)) Set.univ _ M
    (Set.subset_univ _)
  intro Z hZ _ I _
  have := LocallyOfFiniteType.isLocallyNoetherian (reducedClosedSubschemeι Z)
  have := idealModule_coherent I
  exact finitePushforward_ample_coherent_vanishing f (reducedClosedSubschemeι Z)
    hL (hclosed Z hZ) (idealModule I)

include f in
/-- Ampleness is detected on the reduced irreducible components, including nilpotent schemes. -/
theorem ampleLineBundle_iff_on_irreducibleComponents (hL : LocallyFreeRankOne L) :
    AmpleLineBundle L ↔ ∀ Z : Closeds X, (Z : Set X) ∈ irreducibleComponents X →
      AmpleLineBundle ((pullback (reducedClosedSubschemeι Z)).obj L) := by
  constructor
  · intro h Z _
    exact h.pullback_affine (reducedClosedSubschemeι Z)
  · intro h
    have := Chow.source_isNoetherian f
    have hall (Z : Closeds X) (hZ : IsIrreducible (Z : Set X)) :
        AmpleLineBundle ((pullback (reducedClosedSubschemeι Z)).obj L) := by
      obtain ⟨W, hW, hZW⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible (Z : Set X) hZ
      let W' : Closeds X := ⟨W, isClosed_of_mem_irreducibleComponents W hW⟩
      exact ample_reducedClosed_of_le Z W' hZW (h W' hW)
    apply ampleLineBundle_of_ideal_h1_vanishing_anyBase hL
    intro I
    have := idealModule_coherent I
    obtain ⟨n, hn⟩ := eventualTwistVanishing_of_integral_restrictions f hL hall (idealModule I)
    exact ⟨max 1 n, lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _),
      hn (max 1 n) (le_max_right _ _) 0⟩

end FLT.Mazur.FCurve
