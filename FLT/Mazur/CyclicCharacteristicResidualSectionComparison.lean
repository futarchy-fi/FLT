/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicFiniteResidualSections
public import FLT.Mazur.CyclicCharacteristicOppositeLocallyRinged
public import FLT.Mazur.CyclicCharacteristicResidualSectionReconstruction

/-!
# Comparing actual invariant functions with residual reconstruction

The actual invariant-sheaf pullback on the opposite chart is exactly the
regular function reconstructed from the selected chart by fppf descent.
The selected-chart pullback also descends to the full residual section ring
of the existing finite quotient.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- Actual invariant sections pulled back to the opposite characteristic overlap. -/
def oppositeInvariantSectionMap (b : Bool) :
    (invariantSheaf n).obj.obj (op (integerOpen n (chartInteger (!b)))) ⟶
      Γ((transitionOpen n b).toScheme, ⊤) :=
  (invariantOpenSectionsIso n _).inv ≫
    LocallyRingedSpace.Γ.map (oppositeToInvariantOpen n b).op

/-- Their values on transition sources are the original selected-chart pullbacks. -/
theorem oppositeInvariantSectionMap_transition (b : Bool) (i : (transitionCover n b).I₀) :
    oppositeInvariantSectionMap n b ≫ ((transitionCover n b).f i).appTop =
      chartInvariantSectionMap n (!b) ≫ (transitionTarget n b i).appTop := by
  have h := congrArg (fun f => LocallyRingedSpace.Γ.map f.op)
    (oppositeToInvariantOpen_transition n b i)
  change LocallyRingedSpace.Γ.map ((oppositeToInvariantOpen n b).op ≫
    ((transitionCover n b).f i).toLRSHom.op) =
      LocallyRingedSpace.Γ.map ((chartToInvariantOpen n (!b)).op ≫
        (transitionTarget n b i).toLRSHom.op) at h
  simp only [Functor.map_comp] at h
  exact congrArg ((invariantOpenSectionsIso n _).inv ≫ ·) h

/-- Opposite-chart pullback is forced by full residual reconstruction from the selected chart. -/
theorem oppositeInvariantSectionMap_reconstruction (b : Bool)
    (s : (invariantSheaf n).obj.obj (op (integerOpen n (chartInteger (!b))))) :
    oppositeInvariantSectionMap n b s =
      residualSectionReconstruction n b (chartResidualSectionMap n (!b) s) := by
  apply residualSectionReconstruction_unique
  intro i
  exact congrArg (fun f => f s) (oppositeInvariantSectionMap_transition n b i)

/-- The actual invariant section comparison into the residual ring of the finite quotient. -/
def finiteInvariantSectionMap (b : Bool) :
    (invariantSheaf n).obj.obj (op (integerOpen n (chartInteger b))) →+*
      finiteResidualSections n b :=
  (finiteResidualSectionsEquiv n b).symm.toRingHom.comp (chartResidualSectionMap n b)

/-- Its pullback is exactly the original normalized-chart section map. -/
theorem finiteInvariantSectionMap_pullback (b : Bool)
    (s : (invariantSheaf n).obj.obj (op (integerOpen n (chartInteger b)))) :
    (normalizedQuotientMap n b).appTop (finiteInvariantSectionMap n b s).val =
      chartInvariantSectionMap n b s := by
  rw [← finiteResidualSectionsEquiv_val]
  change ((finiteResidualSectionsEquiv n b)
    ((finiteResidualSectionsEquiv n b).symm (chartResidualSectionMap n b s))).val = _
  rw [RingEquiv.apply_symm_apply]
  rfl

/-- Equal selected-chart values imply equal actual values on the opposite overlap. -/
theorem oppositeInvariantSectionMap_eq_of_chart (b : Bool)
    {s t : (invariantSheaf n).obj.obj (op (integerOpen n (chartInteger (!b))))}
    (h : chartInvariantSectionMap n (!b) s = chartInvariantSectionMap n (!b) t) :
    oppositeInvariantSectionMap n b s = oppositeInvariantSectionMap n b t := by
  rw [oppositeInvariantSectionMap_reconstruction, oppositeInvariantSectionMap_reconstruction]
  exact congrArg (residualSectionReconstruction n b) (Subtype.ext h)

end FLT.Mazur.CyclicCharacteristicOrbit
