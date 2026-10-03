/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.AdicRingFunctor
public import FLT.PadicHodgeTheory.ComplexLocalizedGalois

/-! # The Galois action on the actual completed de Rham ring -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- Act on B_dR^+ through the actual finite theta-adic quotients. -/
def complexDeRhamGalois (σ : PadicGalois p) : ComplexBDeRhamPlus p →+* ComplexBDeRhamPlus p :=
  adicRingMap (ComplexDeRhamIdeal p) (complexLocalizedGalois p σ)
    (complexLocalizedGalois_ideal p σ)

/-- The completed action extends the localized Witt action. -/
@[simp] theorem complexDeRhamGalois_algebraMap (σ : PadicGalois p) (x : ComplexAinfInvertP p) :
    complexDeRhamGalois p σ (algebraMap (ComplexAinfInvertP p) (ComplexBDeRhamPlus p) x) =
      algebraMap (ComplexAinfInvertP p) (ComplexBDeRhamPlus p) (complexLocalizedGalois p σ x) :=
  adicRingMap_algebraMap _ _ _ _

/-- Identity on the actual B_dR^+. -/
@[simp] theorem complexDeRhamGalois_one (x : ComplexBDeRhamPlus p) :
    complexDeRhamGalois p 1 x = x := by
  unfold complexDeRhamGalois
  simp only [complexLocalizedGalois_one]
  exact adicRingMap_id _ _ x

/-- Composition on the actual B_dR^+. -/
theorem complexDeRhamGalois_mul (σ τ : PadicGalois p) (x : ComplexBDeRhamPlus p) :
    complexDeRhamGalois p (σ * τ) x =
      complexDeRhamGalois p σ (complexDeRhamGalois p τ x) := by
  unfold complexDeRhamGalois
  simp only [complexLocalizedGalois_mul]
  exact adicRingMap_comp _ _ _ _ _ _ x

/-- The completed ring carries the actual Galois action. -/
instance instMulSemiringActionComplexDeRham :
    MulSemiringAction (PadicGalois p) (ComplexBDeRhamPlus p) where
  smul σ x := complexDeRhamGalois p σ x
  one_smul := complexDeRhamGalois_one p
  mul_smul := complexDeRhamGalois_mul p
  smul_zero σ := map_zero (complexDeRhamGalois p σ)
  smul_add σ := map_add (complexDeRhamGalois p σ)
  smul_one σ := map_one (complexDeRhamGalois p σ)
  smul_mul σ := map_mul (complexDeRhamGalois p σ)

/-- Every action map is a ring automorphism, with the prescribed inverse action. -/
def complexDeRhamGaloisEquiv (σ : PadicGalois p) : ComplexBDeRhamPlus p ≃+* ComplexBDeRhamPlus p :=
  MulSemiringAction.toRingEquiv (PadicGalois p) (ComplexBDeRhamPlus p) σ

/-- The bundled automorphism is the actual completed map. -/
@[simp] theorem complexDeRhamGaloisEquiv_apply (σ : PadicGalois p) (x : ComplexBDeRhamPlus p) :
    complexDeRhamGaloisEquiv p σ x = complexDeRhamGalois p σ x := rfl

end PadicHodgeTheory
