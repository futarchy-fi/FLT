/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearTorusSpecializationPair
public import FLT.Mazur.WeierstrassCoefficientShearRetainedLineSpecialization
import all FLT.Mazur.WeierstrassCoefficientShearRetainedLineSpecialization
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber

/-!
# Both signed retained line actions under coefficient specialization

Apply the actual torus specialization to the independently constructed full
line embeddings. The affine parameter and the signed tangent are retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S T : Type) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  (f : S →ₐ[R] T) (r : S) (k : ℕ) (hk : k + 1 ≤ n)
  (m : ℕ) (hm : k + 1 + m ≤ n)
  (a : Sˣ) (b : Tˣ) (hab : Units.map f.toRingHom a = b)
local notation "V" => W.map (algebraMap R S)
local notation "U" => W.map (algebraMap R T)
variable (ha : (a : S) = (W.map (algebraMap R S)).a₁ + 2 * r)
  (hr : r ^ 2 + (W.map (algebraMap R S)).a₁ * r - (W.map (algebraMap R S)).a₂ = 0)
  (h3 : (W.map (algebraMap R S)).a₃ = 0)
  (h4 : (W.map (algebraMap R S)).a₄ = 0) (h6 : (W.map (algebraMap R S)).a₆ = 0)
  (hb : (b : T) = (W.map (algebraMap R T)).a₁ + 2 * f r)
  (hv : (f r) ^ 2 + (W.map (algebraMap R T)).a₁ * f r -
    (W.map (algebraMap R T)).a₂ = 0)
  (g3 : (W.map (algebraMap R T)).a₃ = 0)
  (g4 : (W.map (algebraMap R T)).a₄ = 0) (g6 : (W.map (algebraMap R T)).a₆ = 0)
local notation "gS" => coefficientShearGluedStructure hπ data S r (k + 1 + m) hm
local notation "gT" => coefficientShearGluedStructure hπ data T (f r) (k + 1 + m) hm
local notation "tT" => Over.hom (MultiplicativeGroupScheme.gm T)
local notation "L" => Spec.map (CommRingCat.ofHom (nodalLaurentCoefficientMap f.toRingHom))
local notation "M" => coefficientShearSpecialization hπ data S T r (f r) (k + 1 + m) hm f

variable
  (hs : algebraMap R S (π ^ (start + k)) = 0) (hp : algebraMap R S π = 0)
  (hd3 : algebraMap R S (data ⟨k + 1, by omega⟩).b3 = 0)
  (hd4 : algebraMap R S (data ⟨k + 1, by omega⟩).b4 = 0)
  (gs : algebraMap R T (π ^ (start + k)) = 0) (gp : algebraMap R T π = 0)
  (gd3 : algebraMap R T (data ⟨k + 1, by omega⟩).b3 = 0)
  (gd4 : algebraMap R T (data ⟨k + 1, by omega⟩).b4 = 0)
local notation "US" => rootShearCurve V r
local notation "UT" => rootShearCurve U (f r)
local notation "LS" => coefficientShearRetainedLine hπ data S r (k + 1 + m) hm
  ⟨k, by omega⟩ hs hp hd3 hd4 hr
local notation "LT" => coefficientShearRetainedLine hπ data T (f r) (k + 1 + m) hm
  ⟨k, by omega⟩ gs gp gd3 gd4 hv
local notation "P" => Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f.toRingHom))
variable {Z : Scheme} (p : Z ⟶ (MultiplicativeGroupScheme.gm T).left)
  (z : Z ⟶ Spec (.of (Polynomial T)))

/-- The full first line retains the polynomial coefficient map. -/
theorem coefficientShearLineSpecialization_first :
    (z ≫ LT 0 (middle_first_root UT)) ≫ M =
      (z ≫ P) ≫ LS 0 (middle_first_root US) := by
  simpa only [Category.assoc] using congrArg (z ≫ ·)
    (coefficientShearSpecialization_retainedFirst hπ data S T f r (f r) k hk m hm
      hs hp hd3 hd4 hr gs gp gd3 gd4 hv rfl)

/-- The signed second line retains that same whole polynomial coefficient map. -/
theorem coefficientShearLineSpecialization_second :
    (z ≫ LT (-(UT).a₁) (middle_second_root UT)) ≫ M =
      (z ≫ P) ≫ LS (-(US).a₁) (middle_second_root US) := by
  simpa only [Category.assoc] using congrArg (z ≫ ·)
    (coefficientShearSpecialization_retainedSecond hπ data S T f r (f r) k hk m hm
      hs hp hd3 hd4 hr gs gp gd3 gd4 hv rfl)

include hab in
/-- Specialize the unrestricted action on the original full first line. -/
theorem coefficientShearLineSpecialization_firstAction
    (h : p ≫ tT = (z ≫ LT 0 (middle_first_root UT)) ≫ gT) :
    (pullback.lift p (z ≫ LT 0 (middle_first_root UT)) h ≫
        coefficientShearTorusAction hπ data T (f r) (k + 1 + m) hm b hb hv g3 g4 g6) ≫ M =
      pullback.lift (p ≫ L) ((z ≫ P) ≫ LS 0 (middle_first_root US))
        (by rw [← coefficientShearLineSpecialization_first hπ data S T f r k hk m hm
              hr hv hs hp hd3 hd4 gs gp gd3 gd4 z]
            exact coefficientShearTorusSpecialization_pairCondition
              hπ data S T f r (k + 1 + m) hm p _ h) ≫
          coefficientShearTorusAction hπ data S r (k + 1 + m) hm a ha hr h3 h4 h6 := by
  rw [coefficientShearTorusSpecialization_pairAction
    hπ data S T f r (k + 1 + m) hm a b hab ha hr h3 h4 h6 hb hv g3 g4 g6]
  congr 1
  apply pullback.hom_ext
  · simp only [pullback.lift_fst]
  · simpa only [pullback.lift_snd] using
      coefficientShearLineSpecialization_first hπ data S T f r k hk m hm hr hv
        hs hp hd3 hd4 gs gp gd3 gd4 z

include hab in
/-- Specialize the unrestricted action on the original full signed second line. -/
theorem coefficientShearLineSpecialization_secondAction
    (h : p ≫ tT = (z ≫ LT (-(UT).a₁) (middle_second_root UT)) ≫ gT) :
    (pullback.lift p (z ≫ LT (-(UT).a₁) (middle_second_root UT)) h ≫
        coefficientShearTorusAction hπ data T (f r) (k + 1 + m) hm b hb hv g3 g4 g6) ≫ M =
      pullback.lift (p ≫ L) ((z ≫ P) ≫ LS (-(US).a₁) (middle_second_root US))
        (by rw [← coefficientShearLineSpecialization_second hπ data S T f r k hk m hm
              hr hv hs hp hd3 hd4 gs gp gd3 gd4 z]
            exact coefficientShearTorusSpecialization_pairCondition
              hπ data S T f r (k + 1 + m) hm p _ h) ≫
          coefficientShearTorusAction hπ data S r (k + 1 + m) hm a ha hr h3 h4 h6 := by
  rw [coefficientShearTorusSpecialization_pairAction
    hπ data S T f r (k + 1 + m) hm a b hab ha hr h3 h4 h6 hb hv g3 g4 g6]
  congr 1
  apply pullback.hom_ext
  · simp only [pullback.lift_fst]
  · simpa only [pullback.lift_snd] using
      coefficientShearLineSpecialization_second hπ data S T f r k hk m hm hr hv
        hs hp hd3 hd4 gs gp gd3 gd4 z

end FLT.Mazur.WeierstrassDividedDepth
