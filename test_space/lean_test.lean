import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.Deriv
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Pi.Basic
import Mathlib.Topology.Instances.Real

open Real
open Set

noncomputable def putnam_2023_a3_solution : ℝ := Real.pi / 2

theorem putnam_2023_a3
: sInf {r : ℝ | r > 0 ∧ ∃ (f : ℝ → ℝ) (g : ℝ → ℝ),
    Differentiable ℝ f ∧ Differentiable ℝ g ∧
    (∀ x : ℝ, |deriv f x| ≤ |g x| ∧ |deriv g x| ≤ |f x|) ∧
    f 0 > 0 ∧ g 0 = 0 ∧ f r = 0} = putnam_2023_a3_solution :=
  by
  -- Define the set S
  let S : Set ℝ := {r : ℝ | r > 0 ∧ ∃ (f : ℝ → ℝ) (g : ℝ → ℝ),
    Differentiable ℝ f ∧ Differentiable ℝ g ∧
    (∀ x : ℝ, |deriv f x| ≤ |g x| ∧ |deriv g x| ≤ |f x|) ∧
    f 0 > 0 ∧ g 0 = 0 ∧ f r = 0}

  -- Show that pi/2 is a lower bound.
  have h1 : ∀ r ∈ S, r ≥ putnam_2023_a3_solution := by
    intro r hr
    rcases hr with hr_pos ∧ ⟨f, g, hfdiff, hgdiff, hderiv_le, hf0_pos, hg0_eq_0, hfr_eq_0⟩
    have hf_continuous : Continuous f := Differentiable.continuous hfdiff
    have hg_continuous : Continuous g := Differentiable.continuous hgdiff

    -- Suppose r < pi/2 for the sake of contradiction.
    by_contra hcontra
    push_neg at hcontra
    have hlt : r < putnam_2023_a3_solution := hcontra

    -- Define h(x) = f(x)^2 + g(x)^2.
    let h (x : ℝ) := f x ^ 2 + g x ^ 2
    have h_diff : Differentiable ℝ h := by
      apply Differentiable.add
      apply Differentiable.pow (Differentiable.continuous hfdiff) 2
      apply Differentiable.pow (Differentiable.continuous hgdiff) 2
    have h_continuous : Continuous h := Differentiable.continuous h_diff
    have h0_pos : h 0 > 0 := by
      unfold h
      specialize hf0_pos
      have hf0sq_pos : f 0 ^ 2 > 0 := Real.sq_pos_of_pos hf0_pos
      have hg0sq_eq_0 : g 0 ^ 2 = 0 := by
        rw [hg0_eq_0]
        exact Real.sq_zero
      rw [hg0sq_eq_0]
      exact hf0sq_pos
    have h' (x : ℝ) : deriv h x = 2 * f x * deriv f x + 2 * g x * deriv g x := by
      unfold h
      simp
      rw [deriv_add]
      rw [deriv_pow]
      rw [deriv_pow]
      ring
      exact Differentiable.differentiableAt hfdiff
      exact Differentiable.differentiableAt hgdiff
    have habs : ∀ x : ℝ, |deriv h x| ≤ 2 * (f x ^ 2 + g x ^ 2) := by
      intro x
      have h1 : |2 * f x * deriv f x + 2 * g x * deriv g x| ≤ 2 * |f x * deriv f x| + 2 * |g x * deriv g x| := by
        apply abs_add
      have h2 : |f x * deriv f x| = |f x| * |deriv f x| := by
        apply abs_mul
      have h3 : |g x * deriv g x| = |g x| * |deriv g x| := by
        apply abs_mul
      rw [h2] at h1
      rw [h3] at h1
      have h4 : |deriv f x| ≤ |g x| := hderiv_le x
      have h5 : |deriv g x| ≤ |f x| := hderiv_le x
      have h6 : |f x| * |deriv f x| ≤ |f x| * |g x| := by
        apply mul_le_mul_of_nonneg_left h4 (abs_nonneg (f x))
      have h7 : |g x| * |deriv g x| ≤ |g x| * |f x| := by
        apply mul_le_mul_of_nonneg_left h5 (abs_nonneg (g x))
      have h8 : 2 * (|f x| * |g x|) + 2 * (|g x| * |f x|) = 4 * (|f x| * |g x|) := by ring
      have h9 : 2 * (|f x| * |g x|) ≤ 2 * (f x ^ 2 + g x ^ 2) := by
        have h10 : 2 * |f x| * |g x| ≤ |f x| ^ 2 + |g x| ^ 2 := by
          apply le_add_of_nonneg_of_le_of_nonneg
          apply Real.sq_nonneg
          apply Real.sq_nonneg
          have h11 : 0 ≤ |f x| ^ 2 - 2 * |f x| * |g x| + |g x| ^ 2 := by
             have h12: (|f x| - |g x|)^2 ≥ 0 := sq_nonneg (|f x| - |g x|)
             rw[sq] at h12
             ring_nf at h12
             exact h12
          linarith
        linarith
      calc
        |2 * f x * deriv f x + 2 * g x * deriv g x| ≤ 2 * (|f x| * |deriv f x|) + 2 * (|g x| * |deriv g x|) := h1
        _ ≤ 2 * (|f x| * |g x|) + 2 * (|g x| * |f x|) := by linarith
        _ = 4 * (|f x| * |g x|) := h8
        _ ≤ 2 * (f x ^ 2 + g x ^ 2 + f x ^ 2 + g x ^ 2) := by linarith
        _ = 4 * (f x ^ 2 + g x ^ 2) := by ring
        _ = 4 * (f x ^ 2 + g x ^ 2) := by ring
        _ ≤ 4 * (f x ^ 2 + g x ^ 2) := by linarith
        _ = 2 * (2 * (f x ^ 2 + g x ^ 2)) := by ring
        _ = 2 * (2 * (f x ^ 2 + g x ^ 2)) := by ring
        _ = 2 * (2 * (f x ^ 2 + g x ^ 2)) := by ring
        _ ≤ 2 * (2 * (f x ^ 2 + g x ^ 2)) := by linarith
        _ = 2 * (2 * (f x ^ 2 + g x ^ 2)) := by ring
        _ ≤ 2 * (2 * (f x ^ 2 + g x ^ 2)) := by linarith
        _ = 4 * (f x ^ 2 + g x ^ 2) := by ring

    -- Apply Grönwall's inequality.
    have gronwall_lemma : ∀ (y : ℝ → ℝ) (a b t : ℝ),
      (∀ x ∈ Interval.Icc a t, |deriv y x| ≤ b * |y x|) →
      (∀ x ∈ Interval.Icc a t, |y x| ≤ |y a| * exp (b * (x - a))) := by
      sorry

    have h_bound : ∀ x ∈ Interval.Icc 0 r, |deriv h x| ≤ 4 * |h x| := by
      intro x hx
      have hx_nonneg : x ≥ 0 := (Interval.Icc_lower hx)
      have hx_le_r : x ≤ r := (Interval.Icc_upper hx)
      calc
        |deriv h x| ≤ 2 * (f x ^ 2 + g x ^ 2) := by apply habs
        _ = 2 * h x := by unfold h; ring
        _ = 2 * |h x| := by rw [abs_of_pos (by unfold h; apply add_nonneg; apply Real.sq_nonneg; apply Real.sq_nonneg)]
        _ = 2 * |h x| := by
           have h_nonneg : h x ≥ 0 := by
             unfold h
             apply add_nonneg
             apply Real.sq_nonneg
             apply Real.sq_nonneg
           exact abs_of_nonneg h_nonneg
        _ ≤ 4 * |h x| := by linarith
    have h_gronwall : ∀ x ∈ Interval.Icc 0 r, |h x| ≤ |h 0| * exp (4 * (x - 0)) := by
      apply gronwall_lemma h 0 4 r
      exact h_bound

    have hr_eq_0 : h r = 0 := by
      unfold h
      specialize hfr_eq_0
      have hfrsq_eq_0 : f r ^ 2 = 0 := Real.sq_eq_zero.mpr hfr_eq_0
      rw [hfrsq_eq_0]
      rw [add_zero]

      sorry -- We need to show g r = 0. This is not trivial.

    -- Now show that pi/2 is in S
    use Real.cos
    use Real.sin
    constructor
    sorry
  sorry
