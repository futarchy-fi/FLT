/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.OrdinaryUniversalQuotient
public import FLT.GaloisRepresentation.HardlyRamified.QuadraticCharacterLift

/-!
# Universal framed deformations with the constructed quadratic quotient

The target character is the sign lift of the quotient in the actual residual
ordinary filtration. Its reduction is proved, so the closed quotient ring
requires neither a supplied lift character nor a residual matrix-row equation.
-/

@[expose] public noncomputable section
open CategoryTheory IsLocalRing GaloisRepresentation GaloisRepresentation.Extensions
namespace Deformation
open ProartinianCat
universe u
variable (O : Type u) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] [Finite (ResidueField O)]
  {V : Type u} [AddCommGroup V] [Module (residueField (𝓞 := O)) V]
  [TopologicalSpace V] [DiscreteTopology V]
  {ρ : Representation (residueField (𝓞 := O)) G V}
  {α β : G →* (residueField (𝓞 := O))ˣ} (E : OrdinaryFiltration ρ α β)
  (hρ : ∀ x : V, Continuous (fun g : G ↦ ρ g x))
  (hβ : ∀ g, β g ^ 2 = 1)

omit [IsNoetherianRing O] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] [Finite (ResidueField O)] in
/-- The sign lift reduces to the quotient character of the actual filtration. -/
theorem ordinaryQuadraticLift_reduce (g : G) :
    algebraMap O (residueField (𝓞 := O))
      (quadraticCharacterLift β hβ O g : O) = (β g : residueField) :=
  congrArg Units.val (quadraticCharacterLift_reduce β hβ O
    (algebraMap O (residueField (𝓞 := O))) g)

/-- The actual universal closed quotient for this fixed integral character. -/
def ordinaryQuadraticUniversalObject : ProartinianCat O :=
  ordinaryUniversalQuotientObject O G E hρ (quadraticCharacterLift β hβ O)
    (ordinaryQuadraticLift_reduce O G hβ)

/-- Its maps classify the lifts in the constructed frame with the fixed sign quotient. -/
def ordinaryQuadraticUniversalEquiv (A : ProartinianCat O) :
    (ordinaryQuadraticUniversalObject O G E hρ hβ ⟶ A) ≃
      {τ : ContinuousFramedLifts O G (Fin 2) (ordinaryUniversalResidual O G E hρ) A //
        ∀ g j, τ.val g 1 j = if j = 1 then
          algebraMap O A (quadraticCharacterLift β hβ O g : O) else 0} :=
  ordinaryUniversalQuotientEquiv O G E hρ (quadraticCharacterLift β hβ O)
    (ordinaryQuadraticLift_reduce O G hβ) A

end Deformation
