/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneEqualityDescent
public import FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneHomExt
import all FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneHomExt
public import FLT.Mazur.WeierstrassSuccessiveShearTerminalProjectiveStructure
import all FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneEqualityDescent
import all FLT.Mazur.WeierstrassCoefficientShearScaleOneEqualityParameters

/-!
# The full scale-one equality descent preserves the coefficient field

Both the original nonzero-constant conic parameter and the exterior retain their base maps.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R]
  {W : WeierstrassCurve R} {π : R} {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [Field S] [Algebra R S] (r : S)
  (j : ℕ) (hj : j + 1 ≤ n)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "s₀" => π ^ (start + j)
local notation "a" => (rootShearCurve (W.map (algebraMap R S)) r).a₁
local notation "c" => algebraMap R S (Data.b6 d)
local notation "T" => ScalarExtension W s₀ π (Data.b3 d) (Data.b4 d) (Data.b6 d) S

local notation "E" => coefficientShearRetainedScaleOneTensorIso
  data S r (j + 1) hj ⟨j, Nat.lt_succ_self j⟩

variable (hs : algebraMap R S (π ^ (start + j)) = 1) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (Data.b3 (data ⟨j + 1, Nat.lt_succ_of_le hj⟩)) = 0)
  (h4 : algebraMap R S (Data.b4 (data ⟨j + 1, Nat.lt_succ_of_le hj⟩)) = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "C" => tensorShearScaleOneConicImmersion W s₀ π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr
local notation "L" => Spec.map (CommRingCat.ofHom (tensorShearScaleOneIncidenceMap W s₀ π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr).toRingHom)
variable (a₀ : Sˣ) (ha₀ : (a₀ : S) =
    (rootShearCurve (W.map (algebraMap R S)) r).a₁)
  (hc : IsUnit (algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6))
local notation "hu" => Eq.mp (congrArg IsUnit ha₀) (Units.isUnit a₀)
local notation "q" => coefficientShearScaleOneEqualityConicParameter
  data S r j hj hp h3 h4 hc hr a₀ ha₀
variable {Y : Scheme.{u}} (f g : ProjectiveLine.scheme S ⟶ Y)
  (w₁ : ProjectiveLine.zero S ≫ f = ProjectiveLine.zero S ≫ g)
  (w₂ : ProjectiveLine.infinity S ≫ f = ProjectiveLine.infinity S ≫ g)
local notation "N" => ProjectiveLine.left S ≫ (ProjectiveLine.slopeNormalizationIso a₀).hom

/-- The complete original equality conic parameter preserves its coefficient structure. -/
@[reassoc] theorem coefficientShearScaleOneEqualityConicParameter_structure :
    q ≫ ProjectiveLine.toBase S = conicStructure a c := by
  rw [coefficientShearScaleOneEqualityConicParameter, Category.assoc,
    WeierstrassSuccessiveShearTerminal.laurentConicComponentProjectiveIso_inv_structure,
    WeierstrassSuccessiveShearTerminal.laurentConicComponentConic_structure]

variable (p : Y ⟶ Spec (.of S))
  (hf : f ≫ p = ProjectiveLine.toBase S) (hg : g ≫ p = ProjectiveLine.toBase S)

include hf hg in
/-- The entire equality equation descends over the original coefficient field. -/
theorem coefficientShearRetainedScaleOneEqualityDesc_structure :
    coefficientShearRetainedScaleOneEqualityDesc
      data S r j hj hs hp h3 h4 hr a₀ ha₀ hc f g w₁ w₂ ≫ p =
        coefficientShearAtlasStructure data S r (j + 1) hj (.inr ⟨j, Nat.lt_succ_self j⟩) := by
  rw [coefficientShearRetainedScaleOneEqualityDesc]
  apply coefficientShearRetainedScaleOneDesc_structure
  · rw [Category.assoc, hf, coefficientShearScaleOneEqualityConicParameter_structure]
  · simp only [Category.assoc]
    rw [hg, ProjectiveLine.slopeNormalizationIso_base, ProjectiveLine.left_toBase]

end FLT.Mazur.WeierstrassDividedDepth
