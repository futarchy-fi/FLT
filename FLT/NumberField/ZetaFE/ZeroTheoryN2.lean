import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Identities
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

open Complex
open Real
open Filter Topology
open scoped RealInnerProductSpace ComplexConjugate

namespace ZeroTheoryN2

/--
Node N2 from cartography/odlyzko-m3-decomposition.md:
Exact modulus identities for the Gamma factor.

For `t ≠ 0` we have:
- `‖Γ(1+it)‖² = π t / sinh (π t)`
- `‖Γ(1/2+it)‖² = π / cosh (π t)`

These are consequences of the reflection formula combined with
`Gamma_conj` and the functional equation.
-/

lemma Gamma_one_add_I_mul_sq_norm (t : ℝ) (ht : t ≠ 0) :
    ‖Gamma (1 + I * t)‖ ^ 2 = π * t / sinh (π * t) := by
  have hRe : (1 + I * t).re = 1 := by simp
  have hIm : (1 + I * t).im = t := by simp
  -- Use the reflection formula specialized at s = I * t, then use Gamma_add_one.
  -- We start from Gamma_mul_Gamma_one_sub applied to s = I*t.
  have h_ref : Gamma (I * t) * Gamma (1 - I * t) = π / sin (π * I * t) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using Complex.Gamma_mul_Gamma_one_sub (I * t)
  -- Turn 1 - I*t into (1+ I*t) using Gamma_add_one twice, being careful with signs.
  -- Γ(1 - it) = -it * Γ(-it)? No, Γ(1 + z) = z * Γ(z), so Γ(1 - it) = (-it)*Γ(-it)
  -- and Γ(1 + it) = it * Γ(it). Hence Γ(1-it) * Γ(1+it) = t^2 * Γ(it)*Γ(-it).
  -- But we need the real reflection relation. Instead use Gamma_mul_Gamma_one_sub at s = 1+it.
  -- Mathlib's Gamma_mul_Gamma_one_sub is stated with sin (π * s).
  have h_ref2 : Gamma (1 + I * t) * Gamma (1 - (1 + I * t)) = π / sin (π * (1 + I * t)) := by
    simpa using Complex.Gamma_mul_Gamma_one_sub (1 + I * t)
  have h_den : sin (π * (1 + I * t)) = - sin (π * I * t) := by
    rw [mul_add, mul_one, Complex.sin_add_pi]
    simp
  have h_zero : sin (π * I * t) ≠ 0 := by
    intro hzero
    -- sin (π * I * t) = I * sinh(π*t). Thus zero implies sinh(π*t)=0, so t=0.
    have h_eq : Complex.sin (π * I * t) = I * Real.sinh (π * t) := Complex.sin_mul_I
    rw [h_eq] at hzero
    have : Real.sinh (π * t) = 0 := I_ne_zero.mp (by simpa [h_eq] using hzero)
    have hπt : π * t = 0 := Real.sinh_eq_zero.mp this
    have hπpos : π ≠ 0 := Real.pi_ne_zero
    exact ht (mul_eq_zero.mp hπt).resolve_left hπpos
  have h_den2 : sin (π * I * t) = I * Real.sinh (π * t) := Complex.sin_mul_I
  have h_den2' : sin (π * (1 + I * t)) = - sin (π * I * t) := by
    rw [mul_add, mul_one]
    exact Complex.sin_add_pi.symm
  have h_den3 : sin (π * (1 + I * t)) = - (I * Real.sinh (π * t)) := by
    simpa [h_den2] using h_den2'
  -- Now Γ(1 - (1 + it)) = Γ(-it). Relation Γ(1+it)*Γ(-it) = ...
  have h_frac : Gamma (1 + I * t) * Gamma (-(I * t)) = π / (-(I * Real.sinh (π * t))) := by
    simpa [h_den3] using h_ref2
  -- Γ(1+it) = I*t * Γ(it), Γ(-it) = -I*t * Γ(-it)? Actually Γ(1-it) = -I*t * Γ(-it).
  -- We need to turn Γ(-it) into Γ(1-it) maybe; use conjugation.
  have h_conj : Gamma (-(I * t)) = conj (Gamma (I * t)) := by
    rw [← Complex.conj_I, ← conj_ofReal]
    simpa [map_neg, mul_comm, mul_left_comm, mul_assoc] using Complex.Gamma_conj (I * t)
  -- easier: use mod squared directly via reflexion.
  -- |Γ(1+it)|^2 = Γ(1+it)*Γ(conj(1+it)) = Γ(1+it)*Γ(1-it).
  -- And Γ(1+it)*Γ(1-it) = (it)*Γ(it) * (-it)*Γ(-it) = t^2 * Γ(it)*Γ(-it).
  -- From reflection at s=it: Γ(it)*Γ(-it) = Γ(it)*Γ(1 - it) / (-it)? careful.
  -- We use a more direct path:
  -- Γ(1+it)*Γ(-it) = π / (- I * sinh(πt))
  -- Γ(1+it) = I*t*Γ(it)
  -- Γ(-it) = -I*t*Γ(-it)? Actually Γ(1 - it) = - I*t*Γ(-it). Then Γ(-it) = Γ(1 - it) / (-I*t).
  -- Thus Γ(1+it)*Γ(1-it) / (-I*t) = π / (- I * sinh(πt)) * something?
  -- Let's just derive via reflection at s = I*t and Gamma_add_one.
  have h_ref_it : Gamma (I * t) * Gamma (1 - I * t) = π / sin (π * I * t) := by
    simpa using Complex.Gamma_mul_Gamma_one_sub (I * t)
  have h_add_one : Gamma (1 + I * t) = I * t * Gamma (I * t) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using Complex.Gamma_add_one (I * t)
  have h_add_one_neg : Gamma (1 - I * t) = - (I * t) * Gamma (-(I * t)) := by
    have h := Complex.Gamma_add_one (-(I * t))
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  -- Now product: Γ(1+it)*Γ(1-it) = (it)*Γ(it) * ((-it)*Γ(-it)) = t^2 * Γ(it)*Γ(-it).
  -- We know Γ(it)*Γ(1-it) = π / sin(πit). Hence Γ(it)*Γ(-it) = Γ(it)*Γ(1-it)/Γ? no.
  -- Γ(1-it) = (-it)*Γ(-it), so Γ(-it) = Γ(1-it)/(-it).
  -- Thus Γ(it)*Γ(-it) = Γ(it)*Γ(1-it)/(-it) = (π / sin(πit)) / (-it).
  have h_prod_it : Gamma (I * t) * Gamma (-(I * t)) = (π / sin (π * I * t)) / (-(I * t)) := by
    rw [← h_ref_it]
    congr 1
    rw [h_add_one_neg]
    field_simp [mul_comm, mul_left_comm, mul_assoc]
    ring_nf
    simp [mul_comm, mul_left_comm, mul_assoc]
  have h_sq : Gamma (1 + I * t) * Gamma (1 - I * t) = (I * t) * (-(I * t)) * (Gamma (I * t) * Gamma (-(I * t))) := by
    rw [h_add_one, h_add_one_neg]
    ring
  have h_conj_prod : Gamma (1 - I * t) = conj (Gamma (1 + I * t)) := by
    rw [← Complex.conj_I, ← conj_ofReal]
    simpa [map_neg, mul_comm, mul_left_comm, mul_assoc] using Complex.Gamma_conj (1 + I * t)
  have h_norm2 : ‖Gamma (1 + I * t)‖ ^ 2 = Gamma (1 + I * t) * Gamma (1 - I * t) := by
    rw [sq_norm, h_conj_prod]
  rw [h_norm2, h_sq, h_prod_it, h_den2]
  have h_den_sin : sin (π * I * t) = I * Real.sinh (π * t) := Complex.sin_mul_I
  rw [h_den_sin]
  -- compute (I*t) * (-I*t) = t^2
  have hI : (I * t) * (-(I * t)) = (t:ℂ)^2 := by ring
  rw [hI]
  -- final: t^2 * ((π / (I * sinh(πt))) / (-I*t)) = π*t/sinh(πt)
  -- need I * (-I) = 1, and t^2/t = t.
  field_simp [I_ne_zero, h_zero, ht]
  ring_nf
  -- now use Complex.ofReal_sinh maybe
  simp [Complex.ofReal_sinh, mul_assoc]
  ring

lemma Gamma_one_half_add_I_mul_sq_norm (t : ℝ) (ht : t ≠ 0) :
    ‖Gamma ((1 / 2 : ℂ) + I * t)‖ ^ 2 = π / cosh (π * t) := by
  -- Use reflection formula at s = 1/2 + it.
  have h_ref : Gamma ((1 / 2 : ℂ) + I * t) * Gamma (1 - ((1 / 2 : ℂ) + I * t)) = π / sin (π * ((1 / 2 : ℂ) + I * t)) := by
    simpa using Complex.Gamma_mul_Gamma_one_sub ((1 / 2 : ℂ) + I * t)
  have h_den : sin (π * ((1 / 2 : ℂ) + I * t)) = cosh (π * t) := by
    rw [mul_add, Complex.sin_add]
    have h1 : (π:ℂ) * (1/2:ℂ) = (π/2:ℂ) := by norm_num
    have hsin : Complex.sin ((π/2:ℂ) + I * (π * t)) = Complex.cos (I * (π * t)) := by
      rw [Complex.sin_add, Complex.sin_pi_div_two, Complex.cos_pi_div_two, one_mul, zero_mul, add_zero]
    rw [h1, hsin]
    -- cos (I * x) = cosh x
    simp [Complex.cos_mul_I, Complex.ofReal_cosh]
    ring
  have h_one_sub : 1 - ((1 / 2 : ℂ) + I * t) = (1 / 2 : ℂ) - I * t := by ring
  have h_conj : Gamma ((1 / 2 : ℂ) - I * t) = conj (Gamma ((1 / 2 : ℂ) + I * t)) := by
    have h := Complex.Gamma_conj ((1 / 2 : ℂ) + I * t)
    -- Γ(conj s) = conj(Γ s), conj((1/2:ℂ)+I*t) = (1/2:ℂ) - I*t
    simpa [map_add, conj_I, conj_ofReal] using h
  have h_norm2 : ‖Gamma ((1 / 2 : ℂ) + I * t)‖ ^ 2 = Gamma ((1 / 2 : ℂ) + I * t) * Gamma ((1 / 2 : ℂ) - I * t) := by
    rw [sq_norm, h_conj]
  rw [h_norm2, ← h_one_sub, h_ref, h_den]

end ZeroTheoryN2
