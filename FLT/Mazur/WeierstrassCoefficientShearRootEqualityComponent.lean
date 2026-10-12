/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootLaurentOverlap
public import FLT.Mazur.WeierstrassSuccessiveShearTerminalProjectiveStructure
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber

/-!
# Independent nonsingular terminal projective component at an arbitrary root

Map the completed conic/Laurent gluing into the actual coefficient model.
The entire terminal torus, both conic attachments and the field structure
remain at the original final stage.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [Field S] [Algebra R S] (r : S) (j : ℕ) (hj : j + 1 ≤ n)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
variable (hs : algebraMap R S (π ^ (start + j)) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4 = 0)
  (hc : IsUnit (algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6))
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "U" => rootShearCurve (W.map (algebraMap R S)) r
local notation "c" => algebraMap R S (Data.b6 d)
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "hsNext" => show algebraMap R S (π ^ (start + (j + 1))) = 0 from by
  rw [← Nat.add_assoc, pow_succ, map_mul, hp, mul_zero]
local notation "conic" => coefficientShearRetainedConic hπ data S r (j + 1) hj
  (Fin.mk j (Nat.lt_succ_self j)) hs hp h3 h4 hr
local notation "N" => coefficientShearTerminalLaurent
  hπ data S r (j + 1) hj hsNext h3 h4 hc hr a ha
local notation "G" => coefficientShearGluedIso hπ data S r (j + 1) hj
local notation "ψ" => tensorShearTerminalLaurentConicMap W π (start + j)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr hc a ha
local notation "b" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ))
local notation "inc" => PrincipalOpenTransport.inclusion (conicT (U).a₁ c)
local notation "F" => tensorShearConicBoundaryIso W (π ^ (start + j)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr
local notation "T" => tensorShearTerminalLaurentEquiv W π (start + j)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hp h3 h4 hr hc a ha

local notation "P" => WeierstrassSuccessiveShearTerminal.laurentConicComponent
  W π (start + j) (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr hc a ha
local notation "l" => WeierstrassSuccessiveShearTerminal.laurentConicComponentConic
  W π (start + j) (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr hc a ha
local notation "t" => WeierstrassSuccessiveShearTerminal.laurentConicComponentTorus
  W π (start + j) (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr hc a ha
local notation "p" => WeierstrassSuccessiveShearTerminal.laurentConicComponentStructure
  W π (start + j) (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr hc a ha
local notation "J" => WeierstrassSuccessiveShearTerminal.laurentConicComponentProjectiveIso
  W π (start + j) (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr hc a ha
local notation "g" => coefficientShearGluedStructure hπ data S r (j + 1) hj

/-- The independently completed conic and Laurent charts map to the actual final stage. -/
def coefficientShearRootLaurentComponentMap :
    P ⟶ coefficientShearGlued hπ data S r (j + 1) hj :=
  pushout.desc conic N
    (coefficientShearRootLaurentConic_boundary hπ data S r j hj hs hp h3 h4 hc hr a ha).symm
local notation "M" => coefficientShearRootLaurentComponentMap
  hπ data S r j hj hs hp h3 h4 hc hr a ha

/-- The complete original conic immersion is retained. -/
@[reassoc] theorem coefficientShearRootLaurentComponentMap_conic : l ≫ M = conic :=
  pushout.inl_desc _ _ _

/-- The entire terminal Laurent chart is retained with its actual normalized coordinate. -/
@[reassoc] theorem coefficientShearRootLaurentComponentMap_torus : t ≫ M = N :=
  pushout.inr_desc _ _ _

/-- The full completed component keeps the coefficient structure. -/
@[reassoc] theorem coefficientShearRootLaurentComponentMap_structure : M ≫ g = p := by
  apply pushout.hom_ext
  · change l ≫ M ≫ g = l ≫ p
    rw [coefficientShearRootLaurentComponentMap_conic_assoc,
      coefficientShearRetainedConic_structure,
      WeierstrassSuccessiveShearTerminal.laurentConicComponentConic_structure]
  · change t ≫ M ≫ g = t ≫ p
    rw [coefficientShearRootLaurentComponentMap_torus_assoc,
      coefficientShearTerminalLaurent_structure,
      WeierstrassSuccessiveShearTerminal.laurentConicComponentTorus_structure]

/-- The full nonsingular terminal projective line, constructed from its actual charts. -/
def coefficientShearRootEqualityComponent :
    ProjectiveLine.scheme S ⟶ coefficientShearGlued hπ data S r (j + 1) hj := (J).hom ≫ M
local notation "C" => coefficientShearRootEqualityComponent
  hπ data S r j hj hs hp h3 h4 hc hr a ha

/-- The whole projective component has the original field structure. -/
@[reassoc] theorem coefficientShearRootEqualityComponent_structure :
    C ≫ g = ProjectiveLine.toBase S := by
  rw [coefficientShearRootEqualityComponent, Category.assoc,
    coefficientShearRootLaurentComponentMap_structure,
    WeierstrassSuccessiveShearTerminal.laurentConicComponentProjectiveIso_structure]

/-- The full Laurent torus has exactly the original terminal parameter. -/
@[reassoc] theorem coefficientShearRootEqualityComponent_torus :
    ProjectiveLine.overlapLeft S ≫ ProjectiveLine.left S ≫ C = N := by
  rw [coefficientShearRootEqualityComponent,
    WeierstrassSuccessiveShearTerminal.laurentConicComponentProjectiveIso_torus_assoc,
    coefficientShearRootLaurentComponentMap_torus]

/-- Zero is the first original retained conic attachment. -/
@[reassoc] theorem coefficientShearRootEqualityComponent_zero :
    ProjectiveLine.zero S ≫ C =
      Spec.map (CommRingCat.ofHom (conicFirstIncidencePoint (U).a₁ c hu).toRingHom) ≫
        conic := by
  rw [coefficientShearRootEqualityComponent, ← Category.assoc,
    WeierstrassSuccessiveShearTerminal.laurentConicComponentProjectiveIso_zero]
  change (_ ≫ l) ≫ M = _
  rw [Category.assoc, coefficientShearRootLaurentComponentMap_conic]

/-- Infinity is the opposite original retained conic attachment. -/
@[reassoc] theorem coefficientShearRootEqualityComponent_infinity :
    ProjectiveLine.infinity S ≫ C =
      Spec.map (CommRingCat.ofHom (conicSecondIncidencePoint (U).a₁ c hu).toRingHom) ≫
        conic := by
  rw [coefficientShearRootEqualityComponent, ← Category.assoc,
    WeierstrassSuccessiveShearTerminal.laurentConicComponentProjectiveIso_infinity]
  change (_ ≫ l) ≫ M = _
  rw [Category.assoc, coefficientShearRootLaurentComponentMap_conic]

/-- The independent projective component as an actual map over the coefficient field. -/
def coefficientShearRootEqualityOverComponent :
    PolygonPinching.component S ⟶ Over.mk g :=
  Over.homMk C (coefficientShearRootEqualityComponent_structure
    hπ data S r j hj hs hp h3 h4 hc hr a ha)

end FLT.Mazur.WeierstrassDividedDepth
