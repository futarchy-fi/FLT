/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearNormalForm
public import FLT.Mazur.WeierstrassCoefficientShearGluing
public import FLT.Mazur.WeierstrassSuccessiveXMiddleComponents
public import FLT.Mazur.WeierstrassDividedTerminalParameterStructure

/-!
# Every retained conic and tangent line in the complete equation gluing

The full middle equation maps into each actual retained chart. Its conic and
both original tangent lines cover that chart, retaining the coefficient maps.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (r : S)
  (t : ℕ) (ht : t ≤ n) (i : Fin t)
local notation "d" => data (Fin.mk (i.val + 1) (by omega))
local notation "q" => algebraMap R S
local notation "U" => rootShearCurve (W.map q) r
local notation "a" => WeierstrassCurve.a₁ U
local notation "c" => q (Data.b6 d)
variable (hs : algebraMap R S (π ^ (start + i.val)) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (Data.b3 (data ⟨i.val + 1, by omega⟩)) = 0)
  (h4 : algebraMap R S (Data.b4 (data ⟨i.val + 1, by omega⟩)) = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "e" => coefficientShearMiddleEquiv W (π ^ (start + i.val)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4
local notation "E" => Scheme.Spec.mapIso
  (Iso.op (RingEquiv.toCommRingCatIso (AlgEquiv.toRingEquiv e)))
local notation "G" => coefficientShearGluedIso hπ data S r t ht
local notation "s" => coefficientShearGluedStructure hπ data S r t ht
local notation "h2" => coefficientShear_a₂_zero W S r hr

/-- The entire middle equation occupies its actual retained chart at the final depth. -/
def coefficientShearRetainedFiber :
    Spec (.of (WeierstrassSuccessiveX.Coordinate U 0 0 0 0 c)) ⟶
      coefficientShearGlued hπ data S r t ht :=
  (E).hom ≫ coefficientShearGluedChart hπ data S r t ht (.inr i)

instance coefficientShearRetainedFiber_isOpenImmersion :
    IsOpenImmersion (coefficientShearRetainedFiber hπ data S r t ht i hs hp h3 h4) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- Reconstruction preserves the full retained equation and its original global embedding. -/
theorem coefficientShearRetainedFiber_reconstruction :
    coefficientShearRetainedFiber hπ data S r t ht i hs hp h3 h4 ≫ (G).hom =
      (E).hom ≫ retainedCoefficientShearChart hπ data S r t ht i.val (by omega) := by
  rw [coefficientShearRetainedFiber, Category.assoc, coefficientShearGluedIso_chart]
  rfl

/-- The whole middle chart keeps its actual coefficient morphism. -/
theorem coefficientShearRetainedFiber_structure :
    coefficientShearRetainedFiber hπ data S r t ht i hs hp h3 h4 ≫ s =
      Spec.map (CommRingCat.ofHom
        (algebraMap S (WeierstrassSuccessiveX.Coordinate U 0 0 0 0 c))) := by
  rw [coefficientShearRetainedFiber, Category.assoc, coefficientShearGluedChart_structure]
  exact terminalComponent_algebra_structure (e).toAlgHom

/-- The original entire retained conic in the complete sheared model. -/
def coefficientShearRetainedConic := middleConicImmersion U c h2 ≫
  coefficientShearRetainedFiber hπ data S r t ht i hs hp h3 h4

/-- The original entire horizontal line at the specified sheared tangent slope. -/
def coefficientShearRetainedLine (v : S) (hv : v * (v + a) = 0) :=
  middleLineImmersion U c h2 v hv ≫
    coefficientShearRetainedFiber hπ data S r t ht i hs hp h3 h4

instance coefficientShearRetainedConic_mono :
    Mono (coefficientShearRetainedConic hπ data S r t ht i hs hp h3 h4 hr) :=
  inferInstanceAs (Mono (_ ≫ _))

/-- The conic's ordinary structure is the actual glued coefficient projection. -/
theorem coefficientShearRetainedConic_structure :
    coefficientShearRetainedConic hπ data S r t ht i hs hp h3 h4 hr ≫ s =
      conicStructure a c := by
  rw [coefficientShearRetainedConic, Category.assoc, coefficientShearRetainedFiber_structure]
  exact terminalComponent_algebra_structure (middleConicMap U c h2)

/-- Each whole retained line keeps its ordinary polynomial coefficient map. -/
theorem coefficientShearRetainedLine_structure (v : S) (hv : v * (v + a) = 0) :
    coefficientShearRetainedLine hπ data S r t ht i hs hp h3 h4 hr v hv ≫ s =
      Spec.map (CommRingCat.ofHom (algebraMap S (Polynomial S))) := by
  rw [coefficientShearRetainedLine, Category.assoc, coefficientShearRetainedFiber_structure]
  exact terminalComponent_algebra_structure (middleLineMap U c h2 v hv)

/-- The conic and both full ordered lines exhaust exactly the actual retained equation. -/
theorem coefficientShearRetained_components_cover :
    Set.range (coefficientShearRetainedConic hπ data S r t ht i hs hp h3 h4 hr) ∪
      (Set.range (coefficientShearRetainedLine hπ data S r t ht i hs hp h3 h4 hr
          0 (middle_first_root U)) ∪
        Set.range (coefficientShearRetainedLine hπ data S r t ht i hs hp h3 h4 hr
          (-a) (middle_second_root U))) =
      Set.range (coefficientShearGluedChart hπ data S r t ht (.inr i)) := by
  ext z
  constructor
  · rintro (⟨x, rfl⟩ | ⟨x, rfl⟩ | ⟨x, rfl⟩)
    · exact ⟨(E).hom (middleConicImmersion U c h2 x), rfl⟩
    · exact ⟨(E).hom (middleLineImmersion U c h2 0 (middle_first_root U) x), rfl⟩
    · exact ⟨(E).hom (middleLineImmersion U c h2 (-a) (middle_second_root U) x), rfl⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := (E).hom.homeomorph.surjective x
    rcases middle_components_cover U c h2 y with ⟨z, rfl⟩ | ⟨z, rfl⟩ | ⟨z, rfl⟩
    · exact Or.inl ⟨z, rfl⟩
    · exact Or.inr (Or.inl ⟨z, rfl⟩)
    · exact Or.inr (Or.inr ⟨z, rfl⟩)

end FLT.Mazur.WeierstrassDividedDepth
