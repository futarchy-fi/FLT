/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicCoefficientStages
public import FLT.Mazur.FiniteCharacterAdicElements

/-!
# All character coefficients commute with adic coefficient change

These are identities of full character algebras, rather than of reduced supports.
The induced spectrum squares retain both finite and complete coefficient maps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OneGonAdicCharacterTower

variable {R S G : Type} [CommRing R] [CommRing S] [AddCommGroup G]
  (I : Ideal R) (J : Ideal S) (f : R →+* S) (hf : I ≤ J.comap f)

/-- The coefficient homomorphism of full character algebras at one adic order. -/
def stageCharacterCoefficient (m : ℕ) :
    AddMonoidAlgebra (StageRing I m) G →+* AddMonoidAlgebra (StageRing J m) G :=
  AddMonoidAlgebra.mapRingHom G (stageCoefficient I J f hf m)

/-- Character coefficient change commutes with the actual adjacent reductions. -/
theorem stageCharacterCoefficient_restriction (m : ℕ) :
    (characterRestriction J G m).comp (stageCharacterCoefficient I J f hf (m + 1)) =
      (stageCharacterCoefficient I J f hf m).comp (characterRestriction I G m) := by
  unfold characterRestriction stageCharacterCoefficient
  rw [← AddMonoidAlgebra.mapRingHom_comp, ← AddMonoidAlgebra.mapRingHom_comp,
    stageCoefficient_restriction]

/-- The complete coefficient change has the specified finite coefficient reduction. -/
theorem stageCharacterCoefficient_reduction (m : ℕ) :
    (stageCharacterCoefficient I J f hf m).comp (FiniteCharacterAdicElements.reduction I m) =
      (FiniteCharacterAdicElements.reduction J m).comp (AddMonoidAlgebra.mapRingHom G f) := by
  unfold stageCharacterCoefficient FiniteCharacterAdicElements.reduction
  rw [← AddMonoidAlgebra.mapRingHom_comp, ← AddMonoidAlgebra.mapRingHom_comp]
  rfl

/-- The actual character spectra form the adjacent coefficient square. -/
@[reassoc] theorem stageCharacterCoefficient_spec_restriction (m : ℕ) :
    Spec.map (CommRingCat.ofHom (stageCharacterCoefficient (G := G) I J f hf m)) ≫
      Spec.map (CommRingCat.ofHom (characterRestriction I G m)) =
        Spec.map (CommRingCat.ofHom (characterRestriction J G m)) ≫
          Spec.map (CommRingCat.ofHom (stageCharacterCoefficient I J f hf (m + 1))) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h))
    (stageCharacterCoefficient_restriction I J f hf m).symm

/-- Finite character spectra retain the coefficient square over the complete source. -/
@[reassoc] theorem stageCharacterCoefficient_spec_reduction (m : ℕ) :
    Spec.map (CommRingCat.ofHom (FiniteCharacterAdicElements.reduction (G := G) J m)) ≫
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom G f)) =
        Spec.map (CommRingCat.ofHom (stageCharacterCoefficient I J f hf m)) ≫
          Spec.map (CommRingCat.ofHom (FiniteCharacterAdicElements.reduction I m)) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h))
    (stageCharacterCoefficient_reduction I J f hf m).symm

end FLT.Mazur.OneGonAdicCharacterTower
