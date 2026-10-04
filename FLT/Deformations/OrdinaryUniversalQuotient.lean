/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.UniversalLocalQuotient
public import FLT.GaloisRepresentation.Extensions.OrdinaryFramedRepresentation

/-!
# The universal quotient condition in a constructed ordinary frame

The residual row hypothesis is discharged from the given exact filtration.
Only a specified integral character lifting its quotient character is required;
no quotient or nonzero solution in a lifted representation is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory IsLocalRing GaloisRepresentation.Extensions
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

/-- Choose a quotient lift and construct its residual framing from exactness. -/
def ordinaryUniversalResidual : G →ₜ* GL (Fin 2) (residueField (𝓞 := O)) :=
  E.adaptedContinuousMatrixRepresentation (Classical.choose (E.surjective 1))
    (Classical.choose_spec (E.surjective 1)) hρ

variable (χ : G →* Oˣ)
  (hχ : ∀ g, algebraMap O (residueField (𝓞 := O)) (χ g : O) = (β g : residueField))

include hχ
omit [IsNoetherianRing O] [CompactSpace G] [TotallyDisconnectedSpace G]
  [Finite (ResidueField O)] in
/-- The residual solution of the universal row equations is constructed from the filtration. -/
theorem ordinaryUniversalResidual_row (g : G) (j : Fin 2) :
    ordinaryUniversalResidual O G E hρ g 1 j =
      if j = 1 then algebraMap O (residueField (𝓞 := O)) (χ g : O) else 0 := by
  rw [hχ g]
  exact E.adaptedMatrixRepresentation_row _ _ g j

/-- The local-condition ring for the actual ordinary residual representation. -/
def ordinaryUniversalQuotientObject : ProartinianCat O :=
  universalLocalQuotientObject O G (Fin 2) (ordinaryUniversalResidual O G E hρ)
    (MonoidHom.id G) χ 1 (ordinaryUniversalResidual_row O G E hρ χ hχ)

/-- The constructed ring classifies precisely lifts with the chosen quotient character. -/
def ordinaryUniversalQuotientEquiv (A : ProartinianCat O) :
    (ordinaryUniversalQuotientObject O G E hρ χ hχ ⟶ A) ≃
      {τ : ContinuousFramedLifts O G (Fin 2) (ordinaryUniversalResidual O G E hρ) A //
        ∀ g j, τ.val g 1 j = if j = 1 then algebraMap O A (χ g : O) else 0} :=
  universalLocalQuotientEquiv O G (Fin 2) (ordinaryUniversalResidual O G E hρ)
    (MonoidHom.id G) χ 1 (ordinaryUniversalResidual_row O G E hρ χ hχ) A

end Deformation
