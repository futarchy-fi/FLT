/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIncidenceShearNormalForm
public import FLT.Mazur.WeierstrassCoefficientShearGluing
public import FLT.Mazur.WeierstrassModificationXFiberConicGeometry
public import FLT.Mazur.WeierstrassDividedTerminalParameterStructure

/-!
# The original incidence line and exceptional conic in the equation gluing

The normal form maps into the full initial equation. Its line and conic cover
that whole chart, with the actual coefficient structure and reconstruction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (r : S) (j : ℕ) (hj : j ≤ n)
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "q" => algebraMap R S
local notation "U" => rootShearCurve (W.map q) r
local notation "a" => WeierstrassCurve.a₁ U
local notation "c" => q (Data.b6 d)
variable (hs : algebraMap R S (π ^ start) = 0)
  (h3 : algebraMap R S (Data.b3 (data ⟨0, Nat.zero_lt_succ n⟩)) = 0)
  (h4 : algebraMap R S (Data.b4 (data ⟨0, Nat.zero_lt_succ n⟩)) = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "e" => coefficientShearNormalEquiv W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs h3 h4 hr
local notation "E" => Scheme.Spec.mapIso
  (Iso.op (RingEquiv.toCommRingCatIso (AlgEquiv.toRingEquiv e)))
local notation "G" => coefficientShearGluedIso hπ data S r j hj
local notation "s" => coefficientShearGluedStructure hπ data S r j hj

/-- The whole incidence-conic equation in the actual finite equation gluing. -/
def coefficientShearInitialFiber : Spec (.of (FiberCoordinate a c)) ⟶
    coefficientShearGlued hπ data S r j hj :=
  (E).hom ≫ coefficientShearGluedChart hπ data S r j hj (.inl 2)

/-- Reconstruction is the actual initial sheared equation, with all exceptional points. -/
@[reassoc] theorem coefficientShearInitialFiber_reconstruction :
    coefficientShearInitialFiber hπ data S r j hj hs h3 h4 hr ≫ (G).hom =
      (E).hom ≫ globalInitialCoefficientShearChart hπ data S r j hj := by
  rw [coefficientShearInitialFiber, Category.assoc, coefficientShearGluedIso_chart]
  rfl

instance coefficientShearInitialFiber_isOpenImmersion :
    IsOpenImmersion (coefficientShearInitialFiber hπ data S r j hj hs h3 h4 hr) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The normal-form chart still uses the actual extended coefficient map. -/
@[reassoc] theorem coefficientShearInitialFiber_structure :
    coefficientShearInitialFiber hπ data S r j hj hs h3 h4 hr ≫ s =
      Spec.map (CommRingCat.ofHom (algebraMap S (FiberCoordinate a c))) := by
  rw [coefficientShearInitialFiber, Category.assoc, coefficientShearGluedChart_structure]
  exact terminalComponent_algebra_structure (e).toAlgHom

/-- The complete original initial incidence line in the sheared equation gluing. -/
def coefficientShearInitialLine :=
  fiberIncidenceImmersion a c ≫ coefficientShearInitialFiber hπ data S r j hj hs h3 h4 hr

/-- The complete original exceptional conic in the same initial equation. -/
def coefficientShearInitialConic :=
  fiberConicImmersion a c ≫ coefficientShearInitialFiber hπ data S r j hj hs h3 h4 hr

instance coefficientShearInitialConic_mono :
    Mono (coefficientShearInitialConic hπ data S r j hj hs h3 h4 hr) :=
  inferInstanceAs (Mono (_ ≫ _))

/-- The exceptional conic keeps its original coefficient structure. -/
@[reassoc] theorem coefficientShearInitialConic_structure :
    coefficientShearInitialConic hπ data S r j hj hs h3 h4 hr ≫ s =
      conicStructure a c := by
  rw [coefficientShearInitialConic, Category.assoc, coefficientShearInitialFiber_structure]
  exact terminalComponent_algebra_structure (fiberConicMap a c)

/-- The entire incidence line also keeps the same coefficient morphism. -/
@[reassoc] theorem coefficientShearInitialLine_structure :
    coefficientShearInitialLine hπ data S r j hj hs h3 h4 hr ≫ s =
      Spec.map (CommRingCat.ofHom (algebraMap S (Polynomial S))) := by
  rw [coefficientShearInitialLine, Category.assoc, coefficientShearInitialFiber_structure]
  exact terminalComponent_algebra_structure (fiberIncidenceMap a c)

/-- The full line and conic together cover exactly the original initial equation chart. -/
theorem coefficientShearInitial_components_cover :
    Set.range (coefficientShearInitialLine hπ data S r j hj hs h3 h4 hr) ∪
      Set.range (coefficientShearInitialConic hπ data S r j hj hs h3 h4 hr) =
        Set.range (coefficientShearGluedChart hπ data S r j hj (.inl 2)) := by
  ext z
  constructor
  · rintro (⟨x, rfl⟩ | ⟨x, rfl⟩)
    · exact ⟨(E).hom (fiberIncidenceImmersion a c x), rfl⟩
    · exact ⟨(E).hom (fiberConicImmersion a c x), rfl⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := (E).hom.homeomorph.surjective x
    rcases fiber_incidence_conic_cover a c y with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · exact Or.inl ⟨t, rfl⟩
    · exact Or.inr ⟨t, rfl⟩

end FLT.Mazur.WeierstrassDividedDepth
