import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option linter.deprecated false
set_option linter.unusedSimpArgs false
open Real
namespace UPT

noncomputable def delta : Real := π/3 - 1
noncomputable def wiggle : Real := delta
noncomputable def simplestMass : Real := 1

axiom pi_gt_three_ax : π > 3
theorem residual_pos : delta > 0 := by unfold delta; linarith [pi_gt_three_ax]
theorem residual_pos_wiggle : wiggle > 0 := by unfold wiggle delta; linarith [pi_gt_three_ax]

noncomputable def V (Phi v : Real) : Real := (Phi^2 - v^2)^2

-- NEW definition: n + n%2 is same as if n%2=1 then n+1 else n, but omega proves it instantly
def stepS (n : Nat) : Nat := n + n % 2

theorem stepS_even (n : Nat) : stepS n % 2 = 0 := by
  unfold stepS
  omega

theorem stepS_idempotent (n : Nat) : stepS (stepS n) = stepS n := by
  unfold stepS
  have he : (n + n % 2) % 2 = 0 := by omega
  omega

noncomputable def N_H : Real := 47201 - 1000000 * wiggle
theorem additiveWitness : N_H + 1000000 * wiggle = 47201 := by unfold N_H; ring

theorem one_takes_one_iff (v : Real) : V (-v+wiggle) v >0 ↔ v ≠ wiggle/2 := by
  unfold V
  constructor
  · intro h heq
    have h0 : ((-(wiggle/2) + wiggle)^2 - (wiggle/2)^2)^2 = 0 := by ring
    rw [heq] at h
    rw [h0] at h
    linarith
  · intro hne
    have hne_sq : (-v + wiggle)^2 - v^2 ≠ 0 := by
      intro heq
      have h_fact : (-v + wiggle - v) * (-v + wiggle + v) = 0 := by nlinarith
      rcases mul_eq_zero.mp h_fact with h1 | h2
      · have hv : v = wiggle/2 := by linarith
        exact hne hv
      · have hw0 : wiggle = 0 := by linarith
        have hpos : wiggle > 0 := residual_pos_wiggle
        linarith
    exact sq_pos_of_ne_zero hne_sq

end UPT
