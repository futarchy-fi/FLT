/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResolvedOriginalOpen

/-!
# Addition where both supplied contractions are originally smooth

Pull the original smooth group law back to the unchanged divided input source.
This domain includes vertical tangents and self-inverse points. Its output
lifts to every supplied finite resolved model, without choosing a slope.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {W : WeierstrassCurve R} {π : R} {k : ℕ} (d : Data W π k)
  (a c : WeierstrassDilatation.Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "a'" => Spec.map (CommRingCat.ofHom a.toRingHom) ≫ toCurve d
local notation "c'" => Spec.map (CommRingCat.ofHom c.toRingHom) ≫ toCurve d
local notation "V" => integralSmoothOpen W
local notation "s" => integralSmoothStructure W

/-- The actual domain where both original contractions are smooth. -/
def suppliedOriginalSmoothDomain : (Spec (.of S)).Opens := (a' ⁻¹ᵁ V) ⊓ (c' ⁻¹ᵁ V)

local notation "O" => suppliedOriginalSmoothDomain d a c

/-- Restrict either complete input contraction to its actual smooth locus. -/
def suppliedOriginalSmoothInput (b : Bool) : (O).toScheme ⟶ (V).toScheme :=
  if b then
    Scheme.homOfLE _ (show O ≤ a' ⁻¹ᵁ V from inf_le_left) ≫ (a' ∣_ V)
  else Scheme.homOfLE _ (show O ≤ c' ⁻¹ᵁ V from inf_le_right) ≫ (c' ∣_ V)

/-- Restriction preserves the whole original input morphism. -/
@[reassoc] theorem suppliedOriginalSmoothInput_inclusion (b : Bool) :
    suppliedOriginalSmoothInput d a c b ≫ (V).ι = (O).ι ≫ (if b then a' else c') := by
  cases b <;> simp only [suppliedOriginalSmoothInput, Bool.false_eq_true, ↓reduceIte,
    Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc]

/-- Both input restrictions retain the original coefficient point. -/
@[reassoc] theorem suppliedOriginalSmoothInput_structure (b : Bool) :
    suppliedOriginalSmoothInput d a c b ≫ s =
      (O).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  rw [integralSmoothStructure, suppliedOriginalSmoothInput_inclusion_assoc]
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, Category.assoc,
    toCurve_structure, specAlgHom_structure]

/-- The exact two contracted inputs in the original smooth group product. -/
def suppliedOriginalSmoothPair : (O).toScheme ⟶ smoothFactorProduct W :=
  pullback.lift (suppliedOriginalSmoothInput d a c true)
    (suppliedOriginalSmoothInput d a c false) (by
      rw [suppliedOriginalSmoothInput_structure, suppliedOriginalSmoothInput_structure])

/-- The constructed pair retains its complete first input. -/
@[reassoc] theorem suppliedOriginalSmoothPair_fst :
    suppliedOriginalSmoothPair d a c ≫ pullback.fst s s =
      suppliedOriginalSmoothInput d a c true := pullback.lift_fst _ _ _

/-- The constructed pair retains its complete second input. -/
@[reassoc] theorem suppliedOriginalSmoothPair_snd :
    suppliedOriginalSmoothPair d a c ≫ pullback.snd s s =
      suppliedOriginalSmoothInput d a c false := pullback.lift_snd _ _ _

/-- Original smooth addition on the entire actual input domain, including the diagonal. -/
def suppliedOriginalSmoothAddition : (O).toScheme ⟶ (V).toScheme :=
  suppliedOriginalSmoothPair d a c ≫ smoothFactorAddition W

/-- This output keeps the coefficient point of both original inputs. -/
@[reassoc] theorem suppliedOriginalSmoothAddition_structure :
    suppliedOriginalSmoothAddition d a c ≫ s =
      (O).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  rw [suppliedOriginalSmoothAddition, Category.assoc, smoothFactorAddition_structure,
    suppliedOriginalSmoothPair_fst_assoc, suppliedOriginalSmoothInput_structure]

variable [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus

/-- The full smooth sum lifts to the unchanged resolved smooth model. -/
def suppliedOriginalSmoothResolvedAddition : (O).toScheme ⟶ (U).toScheme :=
  suppliedOriginalSmoothAddition d a c ≫ finiteOriginalToResolved hπ data j hj

/-- Contraction recovers the original sum of the exact two input contractions. -/
@[reassoc] theorem suppliedOriginalSmoothResolvedAddition_contraction :
    suppliedOriginalSmoothResolvedAddition d a c hπ data j hj ≫ (U).ι ≫
      finiteGlobalContraction hπ data j hj =
        suppliedOriginalSmoothAddition d a c ≫ (V).ι := by
  rw [suppliedOriginalSmoothResolvedAddition, Category.assoc,
    finiteOriginalToResolved_inclusion_assoc, finiteGlobalSmoothEmbedding_contraction]

/-- The lifted sum retains the original coefficient morphism. -/
@[reassoc] theorem suppliedOriginalSmoothResolvedAddition_structure :
    suppliedOriginalSmoothResolvedAddition d a c hπ data j hj ≫ (U).ι ≫ base =
      (O).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  rw [suppliedOriginalSmoothResolvedAddition, Category.assoc,
    finiteOriginalToResolved_structure, suppliedOriginalSmoothAddition_structure]

end FLT.Mazur.WeierstrassDividedDepth
