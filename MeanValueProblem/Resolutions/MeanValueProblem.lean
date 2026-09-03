import Mathlib

/-!
# Mean value problem

*Reference:*
- [Wikipedia](https://en.wikipedia.org/wiki/Mean_value_problem)
- [The fundamental theorem of algebra and complexity theory](https://www.ams.org/journals/bull/1981-04-01/S0273-0979-1981-14858-8/)
by Steve Smale

Given a complex polynomial $p$ of degree $d ≥ 2$ and a complex number $z$
there is a critical point $c$ of $p$, such that $|p(z)-p(c)|/|z-c| ≤ K* |p'(z)|$ for $K=1$.

The conjecture has been proven for:
* `K = 4`
  [The fundamental theorem of algebra and complexity theory](https://www.ams.org/journals/bull/1981-04-01/S0273-0979-1981-14858-8/)
  by *Steve Smale*
* `K = (d-1)/d` if $p$ has real roots or all the roots of $p$ have the same norm.
  [Critical points and values of complex polynomials](https://doi.org/10.1016/0885-064X(89)90019-8)
  by *David Tischler*
-/

namespace MeanValueProblem

end MeanValueProblem

/- ## Counterexample construction: Defs -/

namespace SmaleConstruction
open Polynomial

noncomputable def z0 : ℂ := 33 / 32 + 2 * Complex.I
noncomputable def radius : ℝ := Real.sqrt 4097
noncomputable def q : ℂ[X] := C ((radius : ℂ)⁻¹) * (X ^ 4 + C (64 * Complex.I))
def K : Set ℂ := {z | ‖q.eval z‖ ≤ 1}
noncomputable def xPoly : ℂ[X] := C ((4097 : ℂ)⁻¹) * (C (64 * Complex.I) * X ^ 4 - C 4096)
noncomputable def S (x : ℂ) : ℂ := (1 + x) ^ (-(1 : ℂ) / 4)
noncomputable def W (z : ℂ) : ℂ := z * S (xPoly.eval z) / S (xPoly.eval 1)
noncomputable def T : ℂ := (64 * Complex.I) / (1 + 64 * Complex.I)
noncomputable def Phi (w : ℂ) : ℂ := w * S (-T * w ^ 4) / S (-T)
noncomputable def Jfun (w : ℂ) : ℂ :=
  w * (1 - T * w ^ 4) - z0 * S (-T) * (1 - T * w ^ 4) / S (-T * w ^ 4)
noncomputable def blaschke (r : ℝ) (w : ℂ) : ℂ := (w - (r : ℂ)) / (1 - (r : ℂ) * w)
noncomputable def modelG (r : ℝ) (z : ℂ) : ℂ := blaschke r (W z) / blaschke r (W z0)
noncomputable def modelF (r : ℝ) (z : ℂ) : ℂ := (z - z0) * modelG r z
noncomputable def basePolynomial (g : ℂ[X]) : ℂ[X] := (X - C z0) * g

def AllBadWitness (p : ℂ[X]) : Prop :=
  2 ≤ p.degree ∧ p.eval 0 = 0 ∧ p.derivative.eval 0 = 1 ∧
    ∀ c : ℂ, p.derivative.eval c = 0 → 1 < ‖p.eval c / c‖

end SmaleConstruction

/- ## Counterexample construction: Geometry -/

/-
# Geometry of the explicit quartic lemniscate

The fourth root used throughout is the principal complex power from `Defs`.
All branch assertions below are proved, rather than postulated.  In particular
no root is chosen afresh when passing between the two coordinates.
-/

namespace SmaleConstruction

open Polynomial Complex Set Metric
open scoped Topology

noncomputable section

/- ## The analytic fourth root -/

lemma one_add_ne_zero_of_norm_lt_one {x : ℂ} (hx : ‖x‖ < 1) : 1 + x ≠ 0 :=
  Complex.slitPlane_ne_zero (Complex.mem_slitPlane_of_norm_lt_one hx)

lemma S_ne_zero {x : ℂ} (hx : ‖x‖ < 1) : S x ≠ 0 := by
  exact Complex.cpow_ne_zero_iff.mpr (Or.inl (one_add_ne_zero_of_norm_lt_one hx))

lemma S_pow_four (x : ℂ) : S x ^ 4 = (1 + x)⁻¹ := by
  unfold S
  rw [← Complex.cpow_mul_nat]
  norm_num [Complex.cpow_neg_one]

lemma one_add_mul_S_pow_four {x : ℂ} (hx : ‖x‖ < 1) : (1 + x) * S x ^ 4 = 1 := by
  rw [S_pow_four, mul_inv_cancel₀ (one_add_ne_zero_of_norm_lt_one hx)]

@[simp] lemma S_zero : S 0 = 1 := by simp [S]

lemma hasDerivAt_S {x : ℂ} (hx : ‖x‖ < 1) :
    HasDerivAt S (-S x / (4 * (1 + x))) x := by
  have h := ((hasDerivAt_id x).const_add 1).cpow_const
    (c := -(1 : ℂ) / 4) (Complex.mem_slitPlane_of_norm_lt_one hx)
  dsimp only [id] at h
  convert h using 1
  rw [Complex.cpow_sub _ _ (one_add_ne_zero_of_norm_lt_one hx), Complex.cpow_one]
  dsimp [S]
  field_simp

lemma deriv_S {x : ℂ} (hx : ‖x‖ < 1) : deriv S x = -S x / (4 * (1 + x)) :=
  (hasDerivAt_S hx).deriv

lemma differentiableOn_S : DifferentiableOn ℂ S (ball 0 1) := by
  intro x hx
  exact (hasDerivAt_S (by simpa using hx)).differentiableAt.differentiableWithinAt

lemma analyticAt_S {x : ℂ} (hx : ‖x‖ < 1) : AnalyticAt ℂ S x :=
  (analyticAt_const.add analyticAt_id).cpow analyticAt_const
    (Complex.mem_slitPlane_of_norm_lt_one hx)

lemma continuousAt_S {x : ℂ} (hx : ‖x‖ < 1) : ContinuousAt S x :=
  (hasDerivAt_S hx).continuousAt

/- ## The polynomial sublevel -/

lemma radius_pos : 0 < radius := by
  exact Real.sqrt_pos.2 (by norm_num)

lemma radius_ne_zero : radius ≠ 0 := ne_of_gt radius_pos

lemma radius_sq : radius ^ 2 = 4097 := by
  exact Real.sq_sqrt (by norm_num)

lemma radius_gt_64 : 64 < radius := by
  nlinarith [radius_sq, radius_pos]

lemma radius_lt_65 : radius < 65 := by
  nlinarith [radius_sq, radius_pos]

lemma radius_coe_ne_zero : (radius : ℂ) ≠ 0 := by
  exact_mod_cast radius_ne_zero

lemma radius_coe_sq : (radius : ℂ) ^ 2 = 4097 := by
  exact_mod_cast radius_sq

lemma q_eval (z : ℂ) : q.eval z = (z ^ 4 + 64 * I) / radius := by
  simp [q, div_eq_mul_inv, mul_comm]

lemma xPoly_eval (z : ℂ) : xPoly.eval z = (64 * I * z ^ 4 - 4096) / 4097 := by
  simp [xPoly, div_eq_mul_inv, mul_comm]

lemma q_eval_norm (z : ℂ) : ‖q.eval z‖ = ‖z ^ 4 + 64 * I‖ / radius := by
  rw [q_eval, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos radius_pos]

lemma mem_K_iff (z : ℂ) : z ∈ K ↔ ‖z ^ 4 + 64 * I‖ ≤ radius := by
  change ‖q.eval z‖ ≤ 1 ↔ _
  rw [q_eval_norm, div_le_iff₀ radius_pos, one_mul]

lemma mem_K_iff_normSq (z : ℂ) : z ∈ K ↔ Complex.normSq (z ^ 4 + 64 * I) ≤ 4097 := by
  rw [mem_K_iff, ← radius_sq, ← Complex.sq_norm]
  exact (sq_le_sq₀ (norm_nonneg _) radius_pos.le).symm

lemma q_norm_lt_one_iff (z : ℂ) : ‖q.eval z‖ < 1 ↔ ‖z ^ 4 + 64 * I‖ < radius := by
  rw [q_eval_norm, div_lt_iff₀ radius_pos, one_mul]

lemma q_norm_lt_one_iff_normSq (z : ℂ) :
    ‖q.eval z‖ < 1 ↔ Complex.normSq (z ^ 4 + 64 * I) < 4097 := by
  rw [q_norm_lt_one_iff, ← radius_sq, ← Complex.sq_norm]
  exact (sq_lt_sq₀ (norm_nonneg _) radius_pos.le).symm

lemma isClosed_K : IsClosed K :=
  isClosed_le q.continuous.norm continuous_const

lemma norm_pow_four_le_of_mem_K {z : ℂ} (hz : z ∈ K) : ‖z‖ ^ 4 ≤ radius + 64 := by
  calc
    ‖z‖ ^ 4 = ‖z ^ 4‖ := (norm_pow _ _).symm
    _ = ‖(z ^ 4 + 64 * I) - 64 * I‖ := by ring_nf
    _ ≤ ‖z ^ 4 + 64 * I‖ + ‖64 * I‖ := norm_sub_le _ _
    _ ≤ radius + 64 := by
      simpa using add_le_add_right ((mem_K_iff z).mp hz) 64

lemma norm_lt_four_of_mem_K {z : ℂ} (hz : z ∈ K) : ‖z‖ < 4 := by
  have h := norm_pow_four_le_of_mem_K hz
  have hn := norm_nonneg z
  by_contra hn4
  have h4 : 4 ≤ ‖z‖ := le_of_not_gt hn4
  have hp : (4 : ℝ) ^ 4 ≤ ‖z‖ ^ 4 := pow_le_pow_left₀ (by norm_num) h4 4
  linarith [radius_lt_65]

lemma isBounded_K : Bornology.IsBounded K := by
  apply (isBounded_closedBall (x := (0 : ℂ)) (r := 4)).subset
  intro z hz
  simpa using (norm_lt_four_of_mem_K hz).le

lemma isCompact_K : IsCompact K := isCompact_iff_isClosed_bounded.mpr ⟨isClosed_K, isBounded_K⟩

lemma z0_normSq : Complex.normSq z0 = 5185 / 1024 := by
  norm_num [z0, Complex.normSq_apply]

lemma z0_quartic_normSq :
    Complex.normSq (z0 ^ 4 + 64 * I) / 4097 =
      (443448860929 : ℝ) / 1099511627776 := by
  norm_num [z0, Complex.normSq_apply, pow_succ, Complex.mul_re, Complex.mul_im]

lemma q_z0_norm_lt_one : ‖q.eval z0‖ < 1 := by
  rw [q_norm_lt_one_iff_normSq]
  have := z0_quartic_normSq
  linarith

lemma z0_mem_K : z0 ∈ K := q_z0_norm_lt_one.le

lemma z0_mem_interior_K : z0 ∈ interior K := by
  apply mem_interior_iff_mem_nhds.mpr
  have h : {z : ℂ | ‖q.eval z‖ < 1} ∈ 𝓝 z0 :=
    (isOpen_lt q.continuous.norm continuous_const).mem_nhds q_z0_norm_lt_one
  exact Filter.mem_of_superset h (fun z hz => (show ‖q.eval z‖ ≤ 1 from hz.le))

lemma q_zero_norm_lt_one : ‖q.eval 0‖ < 1 := by
  rw [q_norm_lt_one_iff]
  simpa using radius_gt_64

lemma zero_mem_K : (0 : ℂ) ∈ K := q_zero_norm_lt_one.le

lemma q_one_norm : ‖q.eval 1‖ = 1 := by
  rw [q_eval_norm]
  have hn : ‖(1 : ℂ) ^ 4 + 64 * I‖ = radius := by
    rw [Complex.norm_def]
    congr 1
    norm_num [Complex.normSq_apply]
  rw [hn, div_self radius_ne_zero]

lemma one_mem_K : (1 : ℂ) ∈ K := q_one_norm.le

lemma q_eval_real_mul (t : ℝ) (z : ℂ) :
    q.eval ((t : ℂ) * z) = (t : ℂ) ^ 4 * q.eval z + (1 - (t : ℂ) ^ 4) * q.eval 0 := by
  simp only [q_eval, zero_pow (by norm_num : 4 ≠ 0), zero_add]
  ring

lemma real_mul_mem_K {z : ℂ} (hz : z ∈ K) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (t : ℂ) * z ∈ K := by
  have ht40 : 0 ≤ t ^ 4 := pow_nonneg ht0 _
  have ht41 : t ^ 4 ≤ 1 := pow_le_one₀ ht0 ht1
  change ‖q.eval ((t : ℂ) * z)‖ ≤ 1
  rw [q_eval_real_mul]
  calc
    _ ≤ ‖(t : ℂ) ^ 4 * q.eval z‖ + ‖(1 - (t : ℂ) ^ 4) * q.eval 0‖ := norm_add_le _ _
    _ = t ^ 4 * ‖q.eval z‖ + (1 - t ^ 4) * ‖q.eval 0‖ := by
      rw [norm_mul, norm_mul, ← Complex.ofReal_pow,
        ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ht40,
        abs_of_nonneg (sub_nonneg.mpr ht41)]
    _ ≤ t ^ 4 * 1 + (1 - t ^ 4) * 1 :=
      add_le_add (mul_le_mul_of_nonneg_left hz ht40)
        (mul_le_mul_of_nonneg_left q_zero_norm_lt_one.le (sub_nonneg.mpr ht41))
    _ = 1 := by ring

lemma starConvex_K : StarConvex ℝ 0 K := by
  intro z hz a b ha hb hab
  simpa [Complex.real_smul] using real_mul_mem_K hz hb (by linarith : b ≤ 1)

lemma isPathConnected_K : IsPathConnected K := starConvex_K.isPathConnected zero_mem_K


/- ## The constants and the domain of the coordinate -/

lemma normal_ne_zero : (1 + 64 * I : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  norm_num at this

lemma norm_normal : ‖(1 + 64 * I : ℂ)‖ = radius := by
  rw [Complex.norm_def]
  congr 1
  norm_num [Complex.normSq_apply]

lemma norm_T : ‖T‖ = 64 / radius := by
  rw [T, norm_div, norm_normal]
  norm_num

lemma norm_T_lt_one : ‖T‖ < 1 := by
  rw [norm_T, div_lt_iff₀ radius_pos, one_mul]
  exact radius_gt_64

lemma one_sub_T : 1 - T = (1 + 64 * I)⁻¹ := by
  unfold T
  field_simp [normal_ne_zero]
  ring

lemma one_sub_T_ne_zero : 1 - T ≠ 0 := by
  rw [one_sub_T]
  exact inv_ne_zero normal_ne_zero

lemma S_neg_T_ne_zero : S (-T) ≠ 0 :=
  S_ne_zero (by simpa using norm_T_lt_one)

lemma xPoly_eq_q (z : ℂ) : xPoly.eval z = (64 * I / radius) * q.eval z := by
  rw [xPoly_eval, q_eval]
  field_simp
  rw [radius_coe_sq]
  ring_nf
  simp [I_sq, add_comm]

lemma norm_xPoly (z : ℂ) : ‖xPoly.eval z‖ = (64 / radius) * ‖q.eval z‖ := by
  rw [xPoly_eq_q, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos radius_pos]
  norm_num

lemma norm_xPoly_lt_one {z : ℂ} (hz : z ∈ K) : ‖xPoly.eval z‖ < 1 := by
  rw [norm_xPoly]
  calc
    _ ≤ (64 / radius) * 1 := mul_le_mul_of_nonneg_left hz (div_nonneg (by norm_num) radius_pos.le)
    _ < 1 := by simpa [norm_T] using norm_T_lt_one

lemma norm_xPoly_one_lt_one : ‖xPoly.eval 1‖ < 1 := norm_xPoly_lt_one one_mem_K

lemma S_xPoly_one_ne_zero : S (xPoly.eval 1) ≠ 0 := S_ne_zero norm_xPoly_one_lt_one

lemma one_add_xPoly (z : ℂ) :
    1 + xPoly.eval z = (1 + 64 * I * z ^ 4) / 4097 := by
  rw [xPoly_eval]
  ring

lemma coordinate_denom_ne_zero {z : ℂ} (hz : ‖xPoly.eval z‖ < 1) :
    1 + 64 * I * z ^ 4 ≠ 0 := by
  have h := one_add_ne_zero_of_norm_lt_one hz
  rw [one_add_xPoly] at h
  exact (div_ne_zero_iff.mp h).1

lemma norm_Phi_argument_lt_one {w : ℂ} (hw : ‖w‖ ≤ 1) : ‖-T * w ^ 4‖ < 1 := by
  rw [norm_mul, norm_neg, norm_pow]
  calc
    ‖T‖ * ‖w‖ ^ 4 ≤ ‖T‖ * 1 :=
      mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hw) (norm_nonneg _)
    _ < 1 := by simpa using norm_T_lt_one

lemma Phi_denom_ne_zero {w : ℂ} (hw : ‖-T * w ^ 4‖ < 1) : 1 - T * w ^ 4 ≠ 0 := by
  simpa [sub_eq_add_neg] using one_add_ne_zero_of_norm_lt_one hw

/- ## Algebraic and differential formulas -/

@[simp] lemma W_zero : W 0 = 0 := by simp [W]

@[simp] lemma W_one : W 1 = 1 := by simp [W, S_xPoly_one_ne_zero]

@[simp] lemma Phi_zero : Phi 0 = 0 := by simp [Phi]

@[simp] lemma Phi_one : Phi 1 = 1 := by simp [Phi, S_neg_T_ne_zero]

lemma W_pow_four (z : ℂ) :
    W z ^ 4 = (1 + 64 * I) * z ^ 4 / (1 + 64 * I * z ^ 4) := by
  rw [W, div_pow, mul_pow, S_pow_four, S_pow_four, one_add_xPoly, one_add_xPoly]
  norm_num
  field_simp

lemma Phi_pow_four (w : ℂ) :
    Phi w ^ 4 = (1 - T) * w ^ 4 / (1 - T * w ^ 4) := by
  rw [Phi, div_pow, mul_pow, S_pow_four, S_pow_four]
  simp only [neg_mul, ← sub_eq_add_neg]
  field_simp

lemma hasDerivAt_xPoly (z : ℂ) :
    HasDerivAt (fun z => xPoly.eval z) (256 * I * z ^ 3 / 4097) z := by
  convert xPoly.hasDerivAt z using 1
  simp [xPoly]
  ring

lemma hasDerivAt_W {z : ℂ} (hz : ‖xPoly.eval z‖ < 1) :
    HasDerivAt W (S (xPoly.eval z) / (S (xPoly.eval 1) * (1 + 64 * I * z ^ 4))) z := by
  have h := ((hasDerivAt_id z).mul ((hasDerivAt_S hz).comp z (hasDerivAt_xPoly z))).div_const
    (S (xPoly.eval 1))
  convert h using 1
  simp only [Function.comp_apply, id_eq, one_mul]
  rw [one_add_xPoly]
  field_simp [S_xPoly_one_ne_zero, coordinate_denom_ne_zero hz]
  ring

lemma deriv_W {z : ℂ} (hz : ‖xPoly.eval z‖ < 1) :
    deriv W z = S (xPoly.eval z) / (S (xPoly.eval 1) * (1 + 64 * I * z ^ 4)) :=
  (hasDerivAt_W hz).deriv

lemma deriv_W_ne_zero {z : ℂ} (hz : z ∈ K) : deriv W z ≠ 0 := by
  rw [deriv_W (norm_xPoly_lt_one hz)]
  exact div_ne_zero (S_ne_zero (norm_xPoly_lt_one hz))
    (mul_ne_zero S_xPoly_one_ne_zero (coordinate_denom_ne_zero (norm_xPoly_lt_one hz)))

lemma analyticAt_W {z : ℂ} (hz : ‖xPoly.eval z‖ < 1) : AnalyticAt ℂ W z := by
  exact (analyticAt_id.mul ((analyticAt_S hz).comp (f := fun z : ℂ => xPoly.eval z)
    (xPoly.differentiable.analyticAt z))).div analyticAt_const S_xPoly_one_ne_zero

lemma analyticOnNhd_W : AnalyticOnNhd ℂ W K := fun _ hz => analyticAt_W (norm_xPoly_lt_one hz)

lemma continuousOn_W : ContinuousOn W K := analyticOnNhd_W.continuousOn

lemma hasDerivAt_Phi {w : ℂ} (hw : ‖-T * w ^ 4‖ < 1) :
    HasDerivAt Phi (S (-T * w ^ 4) / (S (-T) * (1 - T * w ^ 4))) w := by
  have h := ((hasDerivAt_id w).mul ((hasDerivAt_S hw).comp w
    (((hasDerivAt_id w).pow 4).const_mul (-T)))).div_const (S (-T))
  convert h using 1
  simp only [Function.comp_apply, id_eq, one_mul, mul_one, Pi.pow_apply, neg_mul,
    ← sub_eq_add_neg]
  field_simp [S_neg_T_ne_zero, Phi_denom_ne_zero hw]
  ring

lemma deriv_Phi {w : ℂ} (hw : ‖-T * w ^ 4‖ < 1) :
    deriv Phi w = S (-T * w ^ 4) / (S (-T) * (1 - T * w ^ 4)) :=
  (hasDerivAt_Phi hw).deriv

lemma deriv_Phi_ne_zero {w : ℂ} (hw : ‖-T * w ^ 4‖ < 1) : deriv Phi w ≠ 0 := by
  rw [deriv_Phi hw]
  exact div_ne_zero (S_ne_zero hw) (mul_ne_zero S_neg_T_ne_zero (Phi_denom_ne_zero hw))

lemma analyticAt_Phi {w : ℂ} (hw : ‖-T * w ^ 4‖ < 1) : AnalyticAt ℂ Phi w := by
  exact (analyticAt_id.mul ((analyticAt_S hw).comp (f := fun w : ℂ => -T * w ^ 4)
    (analyticAt_const.mul (analyticAt_id.pow 4)))).div analyticAt_const S_neg_T_ne_zero

lemma analyticOnNhd_Phi : AnalyticOnNhd ℂ Phi (closedBall 0 1) := by
  intro w hw
  exact analyticAt_Phi (norm_Phi_argument_lt_one (by simpa using hw))

lemma continuousOn_Phi : ContinuousOn Phi (closedBall 0 1) := analyticOnNhd_Phi.continuousOn

lemma deriv_Phi_one : deriv Phi 1 = 1 + 64 * I := by
  rw [deriv_Phi (by simpa using norm_T_lt_one)]
  simp only [one_pow, mul_one]
  rw [one_sub_T]
  field_simp [S_neg_T_ne_zero]


/- ## The exact disk geometry -/

lemma fourth_power_coordinate_norm_identity (u : ℂ) :
    Complex.normSq ((1 + 64 * I) * u) - Complex.normSq (1 + 64 * I * u) =
      Complex.normSq (u + 64 * I) - 4097 := by
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

lemma norm_W_pow_eight (z : ℂ) :
    ‖W z‖ ^ 8 = Complex.normSq ((1 + 64 * I) * z ^ 4) /
      Complex.normSq (1 + 64 * I * z ^ 4) := by
  have h : ‖W z‖ ^ 8 = Complex.normSq (W z ^ 4) := by
    rw [← Complex.sq_norm, norm_pow]
    ring
  rw [h, W_pow_four, Complex.normSq_div]

lemma norm_W_le_one_iff {z : ℂ} (hz : 1 + 64 * I * z ^ 4 ≠ 0) :
    ‖W z‖ ≤ 1 ↔ z ∈ K := by
  rw [← pow_le_one_iff_of_nonneg (norm_nonneg (W z)) (by norm_num : 8 ≠ 0),
    norm_W_pow_eight, div_le_iff₀ (Complex.normSq_pos.mpr hz), one_mul,
    mem_K_iff_normSq]
  have h := fourth_power_coordinate_norm_identity (z ^ 4)
  constructor <;> intro he <;> linarith

lemma norm_W_lt_one_iff {z : ℂ} (hz : 1 + 64 * I * z ^ 4 ≠ 0) :
    ‖W z‖ < 1 ↔ ‖q.eval z‖ < 1 := by
  rw [← pow_lt_one_iff_of_nonneg (norm_nonneg (W z)) (by norm_num : 8 ≠ 0),
    norm_W_pow_eight, div_lt_iff₀ (Complex.normSq_pos.mpr hz), one_mul,
    q_norm_lt_one_iff_normSq]
  have h := fourth_power_coordinate_norm_identity (z ^ 4)
  constructor <;> intro he <;> linarith

lemma W_mem_closedBall {z : ℂ} (hz : z ∈ K) : W z ∈ closedBall 0 1 := by
  simpa using (norm_W_le_one_iff (coordinate_denom_ne_zero (norm_xPoly_lt_one hz))).mpr hz

lemma W_mapsTo : MapsTo W K (closedBall 0 1) := fun _ hz => W_mem_closedBall hz

lemma norm_W_eq_one_of_q_norm_eq_one {z : ℂ} (hz : ‖q.eval z‖ = 1) : ‖W z‖ = 1 := by
  have hK : z ∈ K := hz.le
  have hle : ‖W z‖ ≤ 1 := by simpa using W_mem_closedBall hK
  apply le_antisymm hle
  by_contra h
  have hlt := (norm_W_lt_one_iff (coordinate_denom_ne_zero (norm_xPoly_lt_one hK))).mp
    (lt_of_not_ge h)
  rw [hz] at hlt
  exact (lt_irrefl _ hlt)

lemma norm_W_z0_lt_one : ‖W z0‖ < 1 :=
  (norm_W_lt_one_iff (coordinate_denom_ne_zero (norm_xPoly_lt_one z0_mem_K))).mpr
    q_z0_norm_lt_one

lemma coordinate_denom_Phi {w : ℂ} (hw : 1 - T * w ^ 4 ≠ 0) :
    1 + 64 * I * Phi w ^ 4 = (1 - T * w ^ 4)⁻¹ := by
  rw [Phi_pow_four]
  field_simp [hw]
  unfold T
  field_simp [normal_ne_zero]
  ring

lemma W_Phi_pow_four {w : ℂ} (hw : 1 - T * w ^ 4 ≠ 0) : W (Phi w) ^ 4 = w ^ 4 := by
  rw [W_pow_four, coordinate_denom_Phi hw, Phi_pow_four, one_sub_T]
  field_simp [hw, normal_ne_zero]
  exact mul_div_cancel_right₀ _ (by simpa [mul_comm] using hw)

lemma norm_W_Phi {w : ℂ} (hw : 1 - T * w ^ 4 ≠ 0) : ‖W (Phi w)‖ = ‖w‖ := by
  apply (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by norm_num : 4 ≠ 0)).mp
  simpa only [norm_pow] using congrArg norm (W_Phi_pow_four hw)

lemma Phi_mem_K {w : ℂ} (hw : ‖w‖ ≤ 1) : Phi w ∈ K := by
  have hP := Phi_denom_ne_zero (norm_Phi_argument_lt_one hw)
  have hD : 1 + 64 * I * Phi w ^ 4 ≠ 0 := by
    rw [coordinate_denom_Phi hP]
    exact inv_ne_zero hP
  apply (norm_W_le_one_iff hD).mp
  rw [norm_W_Phi hP]
  exact hw

lemma Phi_mapsTo : MapsTo Phi (closedBall 0 1) K := by
  intro w hw
  exact Phi_mem_K (by simpa using hw)

lemma W_injOn : InjOn W K := by
  intro z hz y hy hzy
  have hDz := coordinate_denom_ne_zero (norm_xPoly_lt_one hz)
  have hDy := coordinate_denom_ne_zero (norm_xPoly_lt_one hy)
  have h4 := congrArg (fun u : ℂ => u ^ 4) hzy
  change W z ^ 4 = W y ^ 4 at h4
  rw [W_pow_four, W_pow_four] at h4
  have he := (div_eq_div_iff hDz hDy).mp h4
  have he' : (1 + 64 * I) * (z ^ 4 - y ^ 4) = 0 := by
    linear_combination he
  have hpow : z ^ 4 = y ^ 4 := sub_eq_zero.mp ((mul_eq_zero.mp he').resolve_left normal_ne_zero)
  have hx : xPoly.eval z = xPoly.eval y := by simp only [xPoly_eval, hpow]
  unfold W at hzy
  rw [hx] at hzy
  exact mul_right_cancel₀ (S_ne_zero (norm_xPoly_lt_one hy))
    ((div_left_inj' S_xPoly_one_ne_zero).mp hzy)

/- The multiplier has no removable singularity at zero.  Its fourth power is
one, so continuity into a finite set pins down the branch on the whole disk. -/

private def inverseMultiplier (w : ℂ) : ℂ :=
  S (xPoly.eval (Phi w)) * S (-T * w ^ 4) / (S (xPoly.eval 1) * S (-T))

private lemma W_Phi_eq_multiplier (w : ℂ) : W (Phi w) = w * inverseMultiplier w := by
  unfold W inverseMultiplier Phi
  ring

private lemma inverseMultiplier_pow_four {w : ℂ} (hw : ‖w‖ ≤ 1) :
    inverseMultiplier w ^ 4 = 1 := by
  have hP := Phi_denom_ne_zero (norm_Phi_argument_lt_one hw)
  unfold inverseMultiplier
  rw [div_pow, mul_pow, mul_pow, S_pow_four, S_pow_four, S_pow_four, S_pow_four,
    one_add_xPoly, one_add_xPoly, coordinate_denom_Phi hP]
  simp only [neg_mul, ← sub_eq_add_neg, one_pow, mul_one]
  rw [one_sub_T]
  field_simp [hP, normal_ne_zero]

private lemma continuousOn_inverseMultiplier : ContinuousOn inverseMultiplier (closedBall 0 1) := by
  intro w hw
  have hw' : ‖w‖ ≤ 1 := by simpa using hw
  apply ContinuousAt.continuousWithinAt
  unfold inverseMultiplier
  apply ContinuousAt.div_const
  apply ContinuousAt.mul
  · exact (continuousAt_S (norm_xPoly_lt_one (Phi_mem_K hw'))).comp
      (f := fun u : ℂ => xPoly.eval (Phi u))
      (xPoly.continuous.continuousAt.comp (analyticOnNhd_Phi w hw).continuousAt)
  · exact (continuousAt_S (norm_Phi_argument_lt_one hw')).comp
      (f := fun u : ℂ => -T * u ^ 4) (by fun_prop)

private lemma inverseMultiplier_one : inverseMultiplier 1 = 1 := by
  unfold inverseMultiplier
  simp [S_xPoly_one_ne_zero, S_neg_T_ne_zero]

private lemma inverseMultiplier_eq_one {w : ℂ} (hw : ‖w‖ ≤ 1) : inverseMultiplier w = 1 := by
  have hfinite : {u : ℂ | u ^ 4 = 1}.Finite := by
    have hp : (X ^ 4 - C (1 : ℂ)) ≠ 0 := by
      intro hp
      have := congrArg (fun p : ℂ[X] => p.eval 0) hp
      norm_num at this
    simpa [Polynomial.IsRoot, sub_eq_zero] using Polynomial.finite_setOf_isRoot hp
  have hc : IsPreconnected (closedBall (0 : ℂ) 1) :=
    (convex_closedBall (0 : ℂ) 1).isPreconnected
  have hm : MapsTo inverseMultiplier (closedBall 0 1) {u : ℂ | u ^ 4 = 1} := by
    intro u hu
    exact inverseMultiplier_pow_four (by simpa using hu)
  have he := hc.constant_of_mapsTo hfinite.isDiscrete continuousOn_inverseMultiplier hm
    (show w ∈ closedBall 0 1 by simpa using hw) (show (1 : ℂ) ∈ closedBall 0 1 by simp)
  exact he.trans inverseMultiplier_one

lemma W_Phi {w : ℂ} (hw : ‖w‖ ≤ 1) : W (Phi w) = w := by
  rw [W_Phi_eq_multiplier, inverseMultiplier_eq_one hw, mul_one]

lemma Phi_W {z : ℂ} (hz : z ∈ K) : Phi (W z) = z := by
  have hw : ‖W z‖ ≤ 1 := by simpa using W_mem_closedBall hz
  apply W_injOn (Phi_mem_K hw) hz
  exact W_Phi hw

lemma W_surjOn : SurjOn W K (closedBall 0 1) := by
  intro w hw
  exact ⟨Phi w, Phi_mapsTo hw, W_Phi (by simpa using hw)⟩

lemma W_bijOn : BijOn W K (closedBall 0 1) := ⟨W_mapsTo, W_injOn, W_surjOn⟩

lemma W_image_K : W '' K = closedBall 0 1 := W_bijOn.image_eq

lemma Phi_injOn : InjOn Phi (closedBall 0 1) := by
  intro u hu w hw he
  have h := congrArg W he
  simpa only [W_Phi (by simpa using hu), W_Phi (by simpa using hw)] using h

lemma Phi_image_closedBall : Phi '' closedBall 0 1 = K := by
  apply Subset.antisymm
  · exact Phi_mapsTo.image_subset
  · intro z hz
    exact ⟨W z, W_mapsTo hz, Phi_W hz⟩

lemma deriv_W_Phi_mul_deriv_Phi {w : ℂ} (hw : ‖w‖ ≤ 1) :
    deriv W (Phi w) * deriv Phi w = 1 := by
  have hP := Phi_denom_ne_zero (norm_Phi_argument_lt_one hw)
  rw [deriv_W (norm_xPoly_lt_one (Phi_mem_K hw)),
    deriv_Phi (norm_Phi_argument_lt_one hw), coordinate_denom_Phi hP]
  calc
    _ = inverseMultiplier w := by
      unfold inverseMultiplier
      field_simp [hP]
    _ = 1 := inverseMultiplier_eq_one hw

lemma deriv_Phi_W_mul_deriv_W {z : ℂ} (hz : z ∈ K) :
    deriv Phi (W z) * deriv W z = 1 := by
  have h := deriv_W_Phi_mul_deriv_Phi (show ‖W z‖ ≤ 1 by simpa using W_mem_closedBall hz)
  rw [Phi_W hz, mul_comm] at h
  exact h


/- ## The quotient jet at the distinguished boundary point -/

lemma Jfun_eq {w : ℂ} (hw : ‖-T * w ^ 4‖ < 1) :
    Jfun w = (Phi w - z0) / deriv Phi w := by
  rw [deriv_Phi hw]
  unfold Jfun Phi
  have hs : S (-(w ^ 4 * T)) ≠ 0 := by simpa only [neg_mul, mul_comm] using S_ne_zero hw
  field_simp [S_ne_zero hw, hs, S_neg_T_ne_zero, Phi_denom_ne_zero hw]

lemma Jfun_eq_mul_deriv_W {w : ℂ} (hw : ‖w‖ ≤ 1) :
    Jfun w = (Phi w - z0) * deriv W (Phi w) := by
  rw [Jfun_eq (norm_Phi_argument_lt_one hw)]
  have h : deriv W (Phi w) = 1 / deriv Phi w :=
    (eq_div_iff (deriv_Phi_ne_zero (norm_Phi_argument_lt_one hw))).mpr
      (deriv_W_Phi_mul_deriv_Phi hw)
  rw [h, mul_one_div]

lemma analyticAt_Jfun {w : ℂ} (hw : ‖-T * w ^ 4‖ < 1) : AnalyticAt ℂ Jfun w := by
  have hP : AnalyticAt ℂ (fun u : ℂ => 1 - T * u ^ 4) w :=
    analyticAt_const.sub (analyticAt_const.mul (analyticAt_id.pow 4))
  have hS : AnalyticAt ℂ (fun u : ℂ => S (-T * u ^ 4)) w :=
    (analyticAt_S hw).comp (f := fun u : ℂ => -T * u ^ 4)
      (analyticAt_const.mul (analyticAt_id.pow 4))
  exact (analyticAt_id.mul hP).sub ((analyticAt_const.mul hP).div hS (S_ne_zero hw))

lemma analyticOnNhd_Jfun : AnalyticOnNhd ℂ Jfun (closedBall 0 1) := by
  intro w hw
  exact analyticAt_Jfun (norm_Phi_argument_lt_one (by simpa using hw))

lemma continuousOn_Jfun : ContinuousOn Jfun (closedBall 0 1) := analyticOnNhd_Jfun.continuousOn

lemma analyticAt_Jfun_one : AnalyticAt ℂ Jfun 1 := analyticOnNhd_Jfun 1 (by simp)

lemma one_sub_z0 : 1 - z0 = -(1 + 64 * I) / 32 := by
  unfold z0
  ring

lemma Jfun_one : Jfun 1 = -(1 : ℂ) / 32 := by
  rw [Jfun_eq (by simpa using norm_T_lt_one), Phi_one, deriv_Phi_one, one_sub_z0]
  field_simp [normal_ne_zero]

lemma hasDerivAt_Jfun {w : ℂ} (hw : ‖-T * w ^ 4‖ < 1) :
    HasDerivAt Jfun
      (1 - 5 * T * w ^ 4 + 5 * z0 * S (-T) * T * w ^ 3 / S (-T * w ^ 4)) w := by
  have hP : HasDerivAt (fun u : ℂ => 1 - T * u ^ 4) (-4 * T * w ^ 3) w := by
    convert (hasDerivAt_const w 1).sub (((hasDerivAt_id w).pow 4).const_mul T) using 1
    simp
    ring
  have hS : HasDerivAt (fun u : ℂ => S (-T * u ^ 4))
      ((-S (-T * w ^ 4) / (4 * (1 + -T * w ^ 4))) * (-4 * T * w ^ 3)) w := by
    have hx : HasDerivAt (fun u : ℂ => -T * u ^ 4) (-4 * T * w ^ 3) w := by
      convert (((hasDerivAt_id w).pow 4).const_mul (-T)) using 1
      simp
      ring
    exact (hasDerivAt_S hw).comp w hx
  have h := ((hasDerivAt_id w).mul hP).sub
    ((hP.const_mul (z0 * S (-T))).div hS (S_ne_zero hw))
  convert h using 1
  dsimp only [id]
  simp only [neg_mul, ← sub_eq_add_neg]
  field_simp [S_ne_zero hw, Phi_denom_ne_zero hw]
  ring

lemma deriv_Jfun {w : ℂ} (hw : ‖-T * w ^ 4‖ < 1) :
    deriv Jfun w = 1 - 5 * T * w ^ 4 + 5 * z0 * S (-T) * T * w ^ 3 / S (-T * w ^ 4) :=
  (hasDerivAt_Jfun hw).deriv

lemma deriv_Jfun_one : deriv Jfun 1 = 1 + 10 * I := by
  rw [deriv_Jfun (by simpa using norm_T_lt_one)]
  simp only [one_pow, mul_one]
  have he : 5 * z0 * S (-T) * T / S (-T) = 5 * z0 * T := by
    field_simp [S_neg_T_ne_zero]
  rw [he]
  unfold z0 T
  field_simp [normal_ne_zero]
  ring

lemma hasDerivAt_Jfun_one : HasDerivAt Jfun (1 + 10 * I) 1 := by
  rw [← deriv_Jfun_one]
  exact analyticAt_Jfun_one.differentiableAt.hasDerivAt


/- ## Chain-rule interface for the model -/

lemma blaschke_denom_ne_zero {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {w : ℂ} (hw : ‖w‖ ≤ 1) : 1 - (r : ℂ) * w ≠ 0 := by
  have hn : ‖(r : ℂ) * w‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
    exact (mul_le_mul_of_nonneg_left hw hr0).trans_lt (by simpa using hr1)
  intro he
  have he' : (r : ℂ) * w = 1 := (sub_eq_zero.mp he).symm
  rw [he', norm_one] at hn
  exact (lt_irrefl _ hn)

lemma hasDerivAt_blaschke {r : ℝ} {w : ℂ} (hw : 1 - (r : ℂ) * w ≠ 0) :
    HasDerivAt (blaschke r) ((1 - (r : ℂ) ^ 2) / (1 - (r : ℂ) * w) ^ 2) w := by
  have h := ((hasDerivAt_id w).sub_const (r : ℂ)).div
    ((hasDerivAt_const w 1).sub ((hasDerivAt_id w).const_mul (r : ℂ))) hw
  convert h using 1
  dsimp only [id, Pi.sub_apply]
  ring

lemma analyticAt_blaschke {r : ℝ} {w : ℂ} (hw : 1 - (r : ℂ) * w ≠ 0) :
    AnalyticAt ℂ (blaschke r) w :=
  (analyticAt_id.sub analyticAt_const).div
    (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)) hw

lemma hasDerivAt_modelG {r : ℝ} {z : ℂ} (hz : ‖xPoly.eval z‖ < 1)
    (hw : 1 - (r : ℂ) * W z ≠ 0) :
    HasDerivAt (modelG r)
      (((1 - (r : ℂ) ^ 2) / (1 - (r : ℂ) * W z) ^ 2) * deriv W z /
        blaschke r (W z0)) z := by
  exact ((hasDerivAt_blaschke hw).comp z
    (analyticAt_W hz).differentiableAt.hasDerivAt).div_const _

lemma hasDerivAt_modelF {r : ℝ} {z : ℂ} (hz : ‖xPoly.eval z‖ < 1)
    (hw : 1 - (r : ℂ) * W z ≠ 0) :
    HasDerivAt (modelF r)
      (modelG r z + (z - z0) *
        (((1 - (r : ℂ) ^ 2) / (1 - (r : ℂ) * W z) ^ 2) * deriv W z /
          blaschke r (W z0))) z := by
  simpa only [one_mul, id_eq] using
    ((hasDerivAt_id z).sub_const z0).mul (hasDerivAt_modelG hz hw)

lemma analyticAt_modelG {r : ℝ} {z : ℂ} (hz : ‖xPoly.eval z‖ < 1)
    (hw : 1 - (r : ℂ) * W z ≠ 0) : AnalyticAt ℂ (modelG r) z := by
  simpa only [modelG, div_eq_mul_inv] using
    ((analyticAt_blaschke hw).comp (f := W) (analyticAt_W hz)).mul
      (analyticAt_const (v := (blaschke r (W z0))⁻¹))

lemma analyticAt_modelF {r : ℝ} {z : ℂ} (hz : ‖xPoly.eval z‖ < 1)
    (hw : 1 - (r : ℂ) * W z ≠ 0) : AnalyticAt ℂ (modelF r) z :=
  (analyticAt_id.sub analyticAt_const).mul (analyticAt_modelG hz hw)

lemma analyticOnNhd_modelG {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    AnalyticOnNhd ℂ (modelG r) K := by
  intro z hz
  exact analyticAt_modelG (norm_xPoly_lt_one hz)
    (blaschke_denom_ne_zero hr0 hr1 (by simpa using W_mem_closedBall hz))

lemma analyticOnNhd_modelF {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    AnalyticOnNhd ℂ (modelF r) K := by
  intro z hz
  exact analyticAt_modelF (norm_xPoly_lt_one hz)
    (blaschke_denom_ne_zero hr0 hr1 (by simpa using W_mem_closedBall hz))

/-- Exact model derivative in the disk coordinate.  Nonvanishing of the
normalizing Blaschke value is not needed for this algebraic identity. -/
lemma deriv_modelF_Phi {r : ℝ} {w : ℂ} (hw : ‖w‖ ≤ 1)
    (hrw : 1 - (r : ℂ) * w ≠ 0) :
    deriv (modelF r) (Phi w) =
      ((w - (r : ℂ)) * (1 - (r : ℂ) * w) + (1 - (r : ℂ) ^ 2) * Jfun w) /
        (blaschke r (W z0) * (1 - (r : ℂ) * w) ^ 2) := by
  have h := hasDerivAt_modelF (r := r) (norm_xPoly_lt_one (Phi_mem_K hw))
    (by simpa only [W_Phi hw] using hrw)
  rw [h.deriv, modelG, W_Phi hw, Jfun_eq_mul_deriv_W hw]
  by_cases hB : blaschke r (W z0) = 0
  · simp [hB]
  · change (w - (r : ℂ)) / (1 - (r : ℂ) * w) / blaschke r (W z0) +
      (Phi w - z0) * (((1 - (r : ℂ) ^ 2) / (1 - (r : ℂ) * w) ^ 2) *
        deriv W (Phi w) / blaschke r (W z0)) = _
    field_simp [hB, hrw]

lemma deriv_modelF_Phi_of_mem_closedBall {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {w : ℂ} (hw : ‖w‖ ≤ 1) :
    deriv (modelF r) (Phi w) =
      ((w - (r : ℂ)) * (1 - (r : ℂ) * w) + (1 - (r : ℂ) ^ 2) * Jfun w) /
        (blaschke r (W z0) * (1 - (r : ℂ) * w) ^ 2) :=
  deriv_modelF_Phi hw (blaschke_denom_ne_zero hr0 hr1 hw)

end
end SmaleConstruction

/- ## Counterexample construction: DiskExclusion -/

/-
# A zero-free disk expression from a boundary jet

Only a bound on `J` on the closed disk and a quadratic Taylor bound near `1`
are needed. Analyticity at `1` supplies the latter. The proof compares with a
factored quadratic whose two roots lie strictly to the right of the disk;
no root-counting or implicit-function theorem is used.
-/

namespace SmaleConstruction

open Filter Set
open scoped Topology

/-- The first-order Taylor polynomial of an analytic function has a locally
quadratically bounded remainder. -/
theorem disk_quadratic_remainder {J : ℂ → ℂ} {z : ℂ} (hJ : AnalyticAt ℂ J z) :
    ∃ C > 0, ∃ δ > 0, ∀ w : ℂ, ‖w - z‖ < δ →
      ‖J w - J z - deriv J z * (w - z)‖ ≤ C * ‖w - z‖ ^ 2 := by
  obtain ⟨p, hp⟩ := hJ
  have hsum (x : ℂ) : p.partialSum 2 x = J z + deriv J z * x := by
    simp only [FormalMultilinearSeries.partialSum, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add, hp.coeff_zero]
    rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff]
    simp only [pow_one, FormalMultilinearSeries.coeff, smul_eq_mul]
    rw [mul_comm, hp.deriv]
    rfl
  obtain ⟨C, hC, hbound⟩ := (hp.isBigO_sub_partialSum_pow 2).exists_pos
  obtain ⟨δ, hδ, hδbound⟩ := Metric.eventually_nhds_iff.mp hbound.bound
  refine ⟨C, hC, δ, hδ, fun w hw => ?_⟩
  have hb := hδbound (y := w - z) (by simpa only [dist_zero_right] using hw)
  simpa only [hsum, add_sub_cancel, norm_pow, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), sub_add_eq_sub_sub] using hb

/-- If the real part of `y` is at most `-u`, the two imaginary roots of
`y² + s²` give this elementary lower bound. -/
theorem disk_quadratic_norm_lower {y : ℂ} {u s : ℝ}
    (hs : 0 ≤ s) (hy : y.re ≤ -u) :
    u * s ≤ ‖-y ^ 2 - (s : ℂ) ^ 2‖ := by
  let v : ℂ := y - (s : ℂ) * Complex.I
  let w : ℂ := y + (s : ℂ) * Complex.I
  have hv : u ≤ ‖v‖ := by
    have h := Complex.re_le_norm (-v)
    simp only [v, Complex.neg_re, Complex.sub_re, Complex.mul_re,
      Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
      Complex.I_im, zero_mul, sub_zero, norm_neg] at h
    linarith
  have hw : u ≤ ‖w‖ := by
    have h := Complex.re_le_norm (-w)
    simp only [w, Complex.neg_re, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
      Complex.I_im, zero_mul, sub_zero, add_zero, norm_neg] at h
    linarith
  have hdist : 2 * s ≤ ‖v‖ + ‖w‖ := by
    have heq : v - w = -((2 * s : ℝ) : ℂ) * Complex.I := by
      dsimp [v, w]
      push_cast
      ring
    have := norm_sub_le v w
    rw [heq, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (by norm_num) hs), Complex.norm_I, mul_one] at this
    exact this
  have hmul : u * s ≤ ‖v‖ * ‖w‖ := by
    rcases le_total ‖v‖ ‖w‖ with h | h
    · have hsw : s ≤ ‖w‖ := by linarith
      exact mul_le_mul hv hsw hs (norm_nonneg _)
    · have hsv : s ≤ ‖v‖ := by linarith
      calc
        u * s ≤ ‖w‖ * ‖v‖ := mul_le_mul hw hsv hs (norm_nonneg _)
        _ = ‖v‖ * ‖w‖ := mul_comm _ _
  have heq : -y ^ 2 - (s : ℂ) ^ 2 = -(v * w) := by
    dsimp [v, w]
    linear_combination -(s : ℂ) ^ 2 * Complex.I_sq
  simpa only [heq, norm_neg, norm_mul] using hmul

/-- The numerator whose nonvanishing is needed for the model derivative. -/
def diskExpression (J : ℂ → ℂ) (r : ℝ) (w : ℂ) : ℂ :=
  (w - (r : ℂ)) * (1 - (r : ℂ) * w) + (1 - (r : ℂ) ^ 2) * J w

/-- The comparison quadratic for the parameter `r = 1 - t²`. -/
def diskQuadratic (a : ℝ) (β : ℂ) (t : ℝ) (w : ℂ) : ℂ :=
  -(w - 1 - β * (t : ℂ) ^ 2) ^ 2 - 2 * (a : ℂ) * (t : ℂ) ^ 2

lemma disk_expression_identity (J : ℂ → ℂ) (t : ℝ) (w : ℂ) :
    diskExpression J (1 - t ^ 2) w =
      -((1 - t ^ 2 : ℝ) : ℂ) * (w - 1) ^ 2 + (t : ℂ) ^ 4 * w +
        ((2 * t ^ 2 - t ^ 4 : ℝ) : ℂ) * J w := by
  unfold diskExpression
  push_cast
  ring

/-- The global bound forces any putative zero into a disk of radius `O(t)`
about `1`. -/
theorem disk_zero_localizes {J : ℂ → ℂ} {B t : ℝ} {w : ℂ}
    (hB : 0 ≤ B) (ht : 0 ≤ t) (htsq : t ^ 2 ≤ 1 / 2)
    (hw : ‖w‖ ≤ 1) (hJw : ‖J w‖ ≤ B)
    (hz : diskExpression J (1 - t ^ 2) w = 0) :
    ‖w - 1‖ ≤ 2 * (B + 1) * t := by
  have ht4 : t ^ 4 ≤ t ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg t) (show 0 ≤ 1 - t ^ 2 by linarith)]
  have hc : 0 ≤ 2 * t ^ 2 - t ^ 4 := by nlinarith [sq_nonneg t]
  have heq : ((1 - t ^ 2 : ℝ) : ℂ) * (w - 1) ^ 2 =
      (t : ℂ) ^ 4 * w + ((2 * t ^ 2 - t ^ 4 : ℝ) : ℂ) * J w := by
    rw [disk_expression_identity] at hz
    linear_combination -hz
  have hn := norm_add_le ((t : ℂ) ^ 4 * w)
    (((2 * t ^ 2 - t ^ 4 : ℝ) : ℂ) * J w)
  rw [← heq] at hn
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ht, abs_of_nonneg hc,
    abs_of_nonneg (show 0 ≤ 1 - t ^ 2 by linarith)] at hn
  have hu : (1 - t ^ 2) * ‖w - 1‖ ^ 2 ≤ (1 + 2 * B) * t ^ 2 := by
    calc
      _ ≤ t ^ 4 * ‖w‖ + (2 * t ^ 2 - t ^ 4) * ‖J w‖ := hn
      _ ≤ t ^ 4 * 1 + (2 * t ^ 2) * B := by
        gcongr
        · nlinarith [pow_nonneg ht 4]
      _ ≤ (1 + 2 * B) * t ^ 2 := by nlinarith
  have hx2 : ‖w - 1‖ ^ 2 ≤ (2 + 4 * B) * t ^ 2 := by
    have hh := mul_nonneg (show 0 ≤ 1 / 2 - t ^ 2 by linarith)
      (sq_nonneg ‖w - 1‖)
    nlinarith
  have hD : 2 + 4 * B ≤ (2 * (B + 1)) ^ 2 := by nlinarith [sq_nonneg B]
  have hh := mul_le_mul_of_nonneg_right hD (sq_nonneg t)
  have hpos : 0 ≤ 2 * (B + 1) * t := by positivity
  nlinarith

/-- On an `O(t)` neighborhood of `1`, the error from the comparison quadratic
is `O(t⁴)`. The same global bound `B` can be used here. -/
theorem disk_quadratic_error {J : ℂ → ℂ} {a B C D t : ℝ} {β w : ℂ}
    (hC : 0 ≤ C) (ht : 0 ≤ t) (hw : ‖w‖ ≤ 1) (hJw : ‖J w‖ ≤ B)
    (hx : ‖w - 1‖ ≤ D * t)
    (hR : ‖J w + (a : ℂ) - β * (w - 1)‖ ≤ C * ‖w - 1‖ ^ 2) :
    ‖diskExpression J (1 - t ^ 2) w - diskQuadratic a β t w‖ ≤
      ((1 + 2 * C) * D ^ 2 + 1 + B + ‖β‖ ^ 2) * t ^ 4 := by
  have heq : diskExpression J (1 - t ^ 2) w - diskQuadratic a β t w =
      (t : ℂ) ^ 2 * (w - 1) ^ 2 + (t : ℂ) ^ 4 * (w - J w + β ^ 2) +
        2 * (t : ℂ) ^ 2 * (J w + (a : ℂ) - β * (w - 1)) := by
    unfold diskExpression diskQuadratic
    push_cast
    ring
  have hmid : ‖w - J w + β ^ 2‖ ≤ 1 + B + ‖β‖ ^ 2 := by
    calc
      _ ≤ ‖w - J w‖ + ‖β ^ 2‖ := norm_add_le _ _
      _ ≤ (‖w‖ + ‖J w‖) + ‖β ^ 2‖ := add_le_add_left (norm_sub_le _ _) _
      _ ≤ 1 + B + ‖β‖ ^ 2 := by rw [norm_pow]; gcongr
  calc
    _ = ‖(t : ℂ) ^ 2 * (w - 1) ^ 2 + (t : ℂ) ^ 4 * (w - J w + β ^ 2) +
        2 * (t : ℂ) ^ 2 * (J w + (a : ℂ) - β * (w - 1))‖ := congrArg norm heq
    _ ≤ (‖(t : ℂ) ^ 2 * (w - 1) ^ 2‖ +
          ‖(t : ℂ) ^ 4 * (w - J w + β ^ 2)‖) +
          ‖2 * (t : ℂ) ^ 2 * (J w + (a : ℂ) - β * (w - 1))‖ :=
      (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ = t ^ 2 * ‖w - 1‖ ^ 2 + t ^ 4 * ‖w - J w + β ^ 2‖ +
          2 * t ^ 2 * ‖J w + (a : ℂ) - β * (w - 1)‖ := by
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ht, Complex.norm_ofNat]
    _ ≤ t ^ 2 * (D * t) ^ 2 + t ^ 4 * (1 + B + ‖β‖ ^ 2) +
          2 * t ^ 2 * (C * (D * t) ^ 2) := by
      gcongr
      exact hR.trans (by gcongr)
    _ = _ := by ring

/-- On the closed unit disk the comparison quadratic has a cubic lower
bound, positive when `a`, `β.re`, and `t` are positive. -/
theorem disk_quadratic_lower {a t : ℝ} {β w : ℂ}
    (ha : 0 ≤ a) (ht : 0 ≤ t) (hw : ‖w‖ ≤ 1) :
    β.re * Real.sqrt (2 * a) * t ^ 3 ≤ ‖diskQuadratic a β t w‖ := by
  have hy : (w - 1 - β * (t : ℂ) ^ 2).re ≤ -(β.re * t ^ 2) := by
    rw [← Complex.ofReal_pow]
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    linarith [Complex.re_le_norm w]
  have hs : 0 ≤ Real.sqrt (2 * a) * t := mul_nonneg (Real.sqrt_nonneg _) ht
  have hs2 : (((Real.sqrt (2 * a) * t : ℝ) : ℂ)) ^ 2 =
      2 * (a : ℂ) * (t : ℂ) ^ 2 := by
    exact_mod_cast (show (Real.sqrt (2 * a) * t) ^ 2 = 2 * a * t ^ 2 by
      rw [mul_pow, Real.sq_sqrt (by positivity)])
  calc
    _ = (β.re * t ^ 2) * (Real.sqrt (2 * a) * t) := by ring
    _ ≤ ‖-(w - 1 - β * (t : ℂ) ^ 2) ^ 2 -
          ((Real.sqrt (2 * a) * t : ℝ) : ℂ) ^ 2‖ := disk_quadratic_norm_lower hs hy
    _ = ‖diskQuadratic a β t w‖ := by rw [hs2]; rfl

/-- Quantitative-remainder version of disk exclusion. No regularity of `J`
away from `1` is needed: its boundedness on the disk is enough. -/
theorem disk_exclusion_of_bounds {J : ℂ → ℂ} {a B C δ : ℝ} {β : ℂ}
    (ha : 0 < a) (hβ : 0 < β.re) (hB : 0 ≤ B)
    (hbound : ∀ w : ℂ, ‖w‖ ≤ 1 → ‖J w‖ ≤ B)
    (hC : 0 ≤ C) (hδ : 0 < δ)
    (hrem : ∀ w : ℂ, ‖w - 1‖ < δ →
      ‖J w + (a : ℂ) - β * (w - 1)‖ ≤ C * ‖w - 1‖ ^ 2) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ w : ℂ, ‖w‖ ≤ 1 → diskExpression J r w ≠ 0 := by
  let D : ℝ := 2 * (B + 1)
  let E : ℝ := (1 + 2 * C) * D ^ 2 + 1 + B + ‖β‖ ^ 2
  let c : ℝ := β.re * Real.sqrt (2 * a)
  have hD : 0 < D := by dsimp [D]; positivity
  have hE : 0 < E := by dsimp [E]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hsmall : (0 : ℝ) < min (1 / 2) (min (δ / D) (c / E)) :=
    lt_min (by norm_num) (lt_min (div_pos hδ hD) (div_pos hc hE))
  obtain ⟨t, ht, htsmall⟩ := exists_between hsmall
  obtain ⟨ht1, htδ, htE⟩ := lt_min_iff.mp htsmall |>.imp_right lt_min_iff.mp
  have htsq : t ^ 2 ≤ 1 / 2 := by nlinarith
  have hDt : D * t < δ := by
    have := (lt_div_iff₀ hD).mp htδ
    linarith
  have hEt : E * t < c := by
    have := (lt_div_iff₀ hE).mp htE
    linarith
  refine ⟨1 - t ^ 2, by linarith, by nlinarith [sq_pos_of_pos ht], ?_⟩
  intro w hw hz
  have hx : ‖w - 1‖ ≤ D * t := disk_zero_localizes hB ht.le htsq hw (hbound w hw) hz
  have hlocal : ‖w - 1‖ < δ := hx.trans_lt hDt
  have herr : ‖diskExpression J (1 - t ^ 2) w - diskQuadratic a β t w‖ ≤ E * t ^ 4 :=
    disk_quadratic_error hC ht.le hw (hbound w hw) hx (hrem w hlocal)
  have hlow : c * t ^ 3 ≤ ‖diskQuadratic a β t w‖ := disk_quadratic_lower ha.le ht.le hw
  rw [hz, zero_sub, norm_neg] at herr
  have hstrict : ‖diskQuadratic a β t w‖ < c * t ^ 3 := by
    calc
      _ ≤ E * t ^ 4 := herr
      _ = (E * t) * t ^ 3 := by ring
      _ < c * t ^ 3 := mul_lt_mul_of_pos_right hEt (pow_pos ht 3)
  exact (not_lt_of_ge hlow) hstrict

/-- Analytic disk exclusion with only a global boundedness hypothesis. -/
theorem disk_exclusion_of_bounded {J : ℂ → ℂ} {a : ℝ}
    (hbounded : ∃ B : ℝ, ∀ w : ℂ, ‖w‖ ≤ 1 → ‖J w‖ ≤ B)
    (hJ : AnalyticAt ℂ J 1) (ha : 0 < a) (hJone : J 1 = -(a : ℂ))
    (hderiv : 0 < (deriv J 1).re) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ w : ℂ, ‖w‖ ≤ 1 →
      (w - (r : ℂ)) * (1 - (r : ℂ) * w) + (1 - (r : ℂ) ^ 2) * J w ≠ 0 := by
  obtain ⟨B, hbound⟩ := hbounded
  have hB : 0 ≤ B := (norm_nonneg (J 0)).trans (hbound 0 (by simp))
  obtain ⟨C, hC, δ, hδ, hrem⟩ := disk_quadratic_remainder hJ
  have hR (w : ℂ) (hw : ‖w - 1‖ < δ) :
      ‖J w + (a : ℂ) - deriv J 1 * (w - 1)‖ ≤ C * ‖w - 1‖ ^ 2 := by
    simpa only [hJone, sub_neg_eq_add] using hrem w hw
  exact disk_exclusion_of_bounds ha hderiv hB hbound hC.le hδ hR

/-- A negative real boundary value and a derivative with positive real part
force the model numerator to be zero-free on the entire closed unit disk,
for some real `r` strictly between `0` and `1`. -/
theorem disk_exclusion {J : ℂ → ℂ} {a : ℝ}
    (hcontinuous : ContinuousOn J (Metric.closedBall (0 : ℂ) 1))
    (hanalytic : AnalyticAt ℂ J 1) (ha : 0 < a) (hJone : J 1 = -(a : ℂ))
    (hderiv : 0 < (deriv J 1).re) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ w : ℂ, ‖w‖ ≤ 1 →
      (w - (r : ℂ)) * (1 - (r : ℂ) * w) + (1 - (r : ℂ) ^ 2) * J w ≠ 0 := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hcontinuous
  apply disk_exclusion_of_bounded ?_ hanalytic ha hJone hderiv
  refine ⟨B, fun w hw => hB w ?_⟩
  simpa only [Metric.mem_closedBall, dist_zero_right] using hw

end SmaleConstruction

/- ## Counterexample construction: Approximation -/

/-
# Polynomial approximation of the Smale model

We use only the binomial series, the geometric series, and Cauchy's estimate.
The closure of polynomial functions is a convenient way to combine finite
truncations without introducing unnecessarily large explicit indices.
-/

namespace SmaleConstruction

open Polynomial Complex Set Metric Filter
open scoped Topology NNReal ENNReal

noncomputable section

namespace PolynomialApproximation

/-- Uniform closure of the complex polynomial functions on a compact set.
No assertion that this is the whole continuous-function algebra is used. -/
def polynomialClosure (s : Set ℂ) [CompactSpace s] : Subalgebra ℂ C(s, ℂ) :=
  (polynomialFunctions s).topologicalClosure

lemma polynomial_mem_closure (s : Set ℂ) [CompactSpace s] (p : ℂ[X]) :
    p.toContinuousMapOn s ∈ polynomialClosure s := by
  apply (polynomialFunctions s).le_topologicalClosure
  change p.toContinuousMapOn s ∈ (polynomialFunctions s : Set C(s, ℂ))
  rw [polynomialFunctions_coe]
  exact ⟨p, rfl⟩

lemma exists_polynomial_near_of_mem_closure {s : Set ℂ} [CompactSpace s]
    {f : C(s, ℂ)} (hf : f ∈ polynomialClosure s) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℂ[X], ∀ z : s, ‖p.eval (z : ℂ) - f z‖ < ε := by
  change f ∈ closure (polynomialFunctions s : Set C(s, ℂ)) at hf
  obtain ⟨p, hp, hdist⟩ := Metric.mem_closure_iff.mp hf ε hε
  rw [polynomialFunctions_coe] at hp
  obtain ⟨p, rfl⟩ := hp
  refine ⟨p, fun z => ?_⟩
  have h := (ContinuousMap.dist_apply_le_dist z).trans_lt hdist
  simpa [dist_eq_norm, norm_sub_rev] using h

/-- A scalar power series on the unit disk can be applied inside the closed
polynomial algebra, provided its argument has norm strictly less than one.
Compactness supplies a single strict subdisk for all arguments. -/
lemma powerSeries_comp_mem_closure {s : Set ℂ} [CompactSpace s]
    {f g : C(s, ℂ)} {F : ℂ → ℂ} {c : ℕ → ℂ}
    (hf : f ∈ polynomialClosure s) (hfnorm : ∀ z : s, ‖f z‖ < 1)
    (hF : HasFPowerSeriesOnBall F (.ofScalars ℂ c) 0 1)
    (hg : ∀ z : s, g z = F (f z)) :
    g ∈ polynomialClosure s := by
  have hnorm : ‖f‖ < 1 := (f.norm_lt_iff zero_lt_one).mpr hfnorm
  obtain ⟨τ, hτ, hτ1⟩ := exists_between hnorm
  let τ' : ℝ≥0 := ⟨τ, (norm_nonneg f).trans hτ.le⟩
  have hτ' : (τ' : ℝ≥0∞) < 1 := by exact_mod_cast hτ1
  have hu := hF.tendstoUniformlyOn hτ'
  let p : ℕ → C(s, ℂ) := fun n => ∑ k ∈ Finset.range n, c k • f ^ k
  have hp : ∀ n, p n ∈ polynomialClosure s := by
    intro n
    exact (polynomialClosure s).sum_mem fun k _ =>
      (polynomialClosure s).smul_mem ((polynomialClosure s).pow_mem hf k) (c k)
  have ht : Tendsto p atTop (𝓝 g) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu ε hε] with n hn
    rw [dist_eq_norm, ContinuousMap.norm_lt_iff _ hε]
    intro z
    have hz : f z ∈ ball (0 : ℂ) (τ' : ℝ) := by
      simpa only [mem_ball, dist_zero_right] using (f.norm_coe_le_norm z).trans_lt hτ
    have h := hn (f z) hz
    simpa [p, FormalMultilinearSeries.partialSum, FormalMultilinearSeries.ofScalars_apply_eq,
      hg z, dist_eq_norm, norm_sub_rev, mul_comm] using h
  exact (polynomialFunctions s).isClosed_topologicalClosure.mem_of_tendsto ht
    (Eventually.of_forall hp)

/-- The geometric-series denominator cannot vanish in the open unit disk. -/
lemma one_sub_ne_zero_of_norm_lt_one {x : ℂ} (hx : ‖x‖ < 1) : 1 - x ≠ 0 := by
  simpa only [← sub_eq_add_neg] using
    (one_add_ne_zero_of_norm_lt_one (x := -x) (by simpa using hx))

/-- Polynomial approximation on any compact set on which both series used in
`modelG` converge. The normalizing constant may even vanish: in that case the
model is identically zero and the assertion still holds. -/
lemma exists_polynomial_modelG_uniform_approx_on {L : Set ℂ} (hL : IsCompact L)
    {r : ℝ} (hx : ∀ z ∈ L, ‖xPoly.eval z‖ < 1)
    (hw : ∀ z ∈ L, ‖(r : ℂ) * W z‖ < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℂ[X], ∀ z ∈ L, ‖p.eval z - modelG r z‖ < ε := by
  letI : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have hSc : ContinuousOn (fun z : ℂ => S (xPoly.eval z)) L := by
    intro z hz
    exact ((continuousAt_S (hx z hz)).comp (f := fun z : ℂ => xPoly.eval z)
      xPoly.continuous.continuousAt).continuousWithinAt
  let Sm : C(L, ℂ) := ⟨fun z => S (xPoly.eval z), hSc.restrict⟩
  have hSm : Sm ∈ polynomialClosure L := by
    apply powerSeries_comp_mem_closure (f := xPoly.toContinuousMapOn L)
      (polynomial_mem_closure L xPoly) (fun z => hx z z.property)
      (show HasFPowerSeriesOnBall S
        (.ofScalars ℂ (Ring.choose (-(1 : ℂ) / 4) ·)) 0 1 from
        Complex.one_add_cpow_hasFPowerSeriesOnBall_zero)
    intro z
    rfl
  have hWc : ContinuousOn W L := fun z hz =>
    (analyticAt_W (hx z hz)).continuousAt.continuousWithinAt
  let Wm : C(L, ℂ) := ⟨fun z => W z, hWc.restrict⟩
  have hWm : Wm ∈ polynomialClosure L := by
    have he : Wm = (S (xPoly.eval 1))⁻¹ • (X.toContinuousMapOn L * Sm) := by
      ext z
      simp [Wm, Sm, W, div_eq_mul_inv, mul_comm]
    rw [he]
    exact (polynomialClosure L).smul_mem
      ((polynomialClosure L).mul_mem (polynomial_mem_closure L X) hSm) _
  have hden : ∀ z ∈ L, 1 - (r : ℂ) * W z ≠ 0 := fun z hz =>
    one_sub_ne_zero_of_norm_lt_one (hw z hz)
  have hIc : ContinuousOn (fun z : ℂ => 1 / (1 - (r : ℂ) * W z)) L :=
    continuousOn_const.div (continuousOn_const.sub (continuousOn_const.mul hWc)) hden
  let Im : C(L, ℂ) := ⟨fun z => 1 / (1 - (r : ℂ) * W z), hIc.restrict⟩
  have hIm : Im ∈ polynomialClosure L := by
    apply powerSeries_comp_mem_closure (f := (r : ℂ) • Wm)
      ((polynomialClosure L).smul_mem hWm (r : ℂ)) (fun z => hw z z.property)
      Complex.one_div_one_sub_hasFPowerSeriesOnBall_zero
    intro z
    rfl
  have hGc : ContinuousOn (modelG r) L := fun z hz =>
    (analyticAt_modelG (hx z hz) (hden z hz)).continuousAt.continuousWithinAt
  let Gm : C(L, ℂ) := ⟨fun z => modelG r z, hGc.restrict⟩
  have hGm : Gm ∈ polynomialClosure L := by
    have he : Gm = (blaschke r (W z0))⁻¹ •
        ((Wm - algebraMap ℂ C(L, ℂ) (r : ℂ)) * Im) := by
      ext z
      change ((W z - (r : ℂ)) / (1 - (r : ℂ) * W z)) / blaschke r (W z0) =
        (blaschke r (W z0))⁻¹ * ((W z - (r : ℂ)) * (1 / (1 - (r : ℂ) * W z)))
      simp only [div_eq_mul_inv, one_mul]
      ring
    rw [he]
    exact (polynomialClosure L).smul_mem
      ((polynomialClosure L).mul_mem
        ((polynomialClosure L).sub_mem hWm ((polynomialClosure L).algebraMap_mem _)) hIm) _
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_mem_closure hGm hε
  exact ⟨p, fun z hz => hp ⟨z, hz⟩⟩

end PolynomialApproximation

/-- A common open domain for the binomial and geometric expansions. -/
def approximationDomain (r : ℝ) : Set ℂ :=
  {z | ‖xPoly.eval z‖ < 1 ∧ ‖(r : ℂ) * W z‖ < 1}

lemma isOpen_approximationDomain (r : ℝ) : IsOpen (approximationDomain r) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have hx := xPoly.continuous.norm.continuousAt.eventually_lt continuousAt_const hz.1
  have hw := (continuousAt_const.mul (analyticAt_W hz.1).continuousAt).norm.eventually_lt
    continuousAt_const hz.2
  exact inter_mem hx hw

lemma K_subset_approximationDomain {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    K ⊆ approximationDomain r := by
  intro z hz
  refine ⟨norm_xPoly_lt_one hz, ?_⟩
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  have hw : ‖W z‖ ≤ 1 := by simpa using W_mem_closedBall hz
  exact (mul_le_mul_of_nonneg_left hw hr0).trans_lt (by simpa using hr1)

lemma analyticOnNhd_modelG_approximationDomain (r : ℝ) :
    AnalyticOnNhd ℂ (modelG r) (approximationDomain r) := by
  intro z hz
  exact analyticAt_modelG hz.1
    (PolynomialApproximation.one_sub_ne_zero_of_norm_lt_one hz.2)

/-- Every model with `0 < r < 1` is approximable by complex polynomials in the
C¹ norm on `K`. The derivative is the formal polynomial derivative evaluated
at the point, so the conclusion is ready for the algebraic construction. -/
lemma exists_polynomial_modelG_C1_approx {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ[X], ∀ z ∈ K,
      ‖g.eval z - modelG r z‖ < ε ∧
      ‖g.derivative.eval z - deriv (modelG r) z‖ < ε := by
  obtain ⟨δ, hδ, hsub⟩ := isCompact_K.exists_cthickening_subset_open
    (isOpen_approximationDomain r) (K_subset_approximationDomain hr0.le hr1)
  obtain ⟨g, hg⟩ := PolynomialApproximation.exists_polynomial_modelG_uniform_approx_on
    (isCompact_K.cthickening (r := δ)) (fun z hz => (hsub hz).1)
    (fun z hz => (hsub hz).2) (lt_min hε (mul_pos hε hδ))
  have hG := analyticOnNhd_modelG_approximationDomain r
  refine ⟨g, fun z hz => ⟨?_, ?_⟩⟩
  · exact (hg z (self_subset_cthickening (δ := δ) K hz)).trans_le (min_le_left _ _)
  · have hball : closedBall z δ ⊆ approximationDomain r :=
      (closedBall_subset_cthickening hz δ).trans hsub
    have hsphere : sphere z δ ⊆ approximationDomain r := sphere_subset_closedBall.trans hball
    have he := Complex.norm_cderiv_sub_lt hδ
      (fun w hw => (hg w (closedBall_subset_cthickening hz δ (sphere_subset_closedBall hw))).trans_le
        (min_le_right _ _)) g.continuous.continuousOn (hG.continuousOn.mono hsphere)
    rw [Complex.cderiv_eq_deriv isOpen_univ g.differentiable.differentiableOn hδ (subset_univ _),
      Complex.cderiv_eq_deriv (isOpen_approximationDomain r) hG.differentiableOn hδ hball,
      Polynomial.deriv, mul_div_cancel_right₀ _ hδ.ne'] at he
    exact he

/-- C¹ approximation with the exact normalization at `z0`. We divide the
approximant by its value at `z0`; continuity of this normalization in the two
sup norms avoids imposing arbitrary explicit approximation degrees. -/
lemma exists_normalized_polynomial_modelG_C1_approx {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (hnorm : modelG r z0 = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ[X], g.eval z0 = 1 ∧ ∀ z ∈ K,
      ‖g.eval z - modelG r z‖ < ε ∧
      ‖g.derivative.eval z - deriv (modelG r) z‖ < ε := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp isCompact_K
  let a : K := ⟨z0, z0_mem_K⟩
  have hG := analyticOnNhd_modelG hr0.le hr1
  let f : C(K, ℂ) := ⟨fun z => modelG r z, hG.continuousOn.restrict⟩
  let d : C(K, ℂ) := ⟨fun z => deriv (modelG r) z, hG.deriv.continuousOn.restrict⟩
  have hf : f a = 1 := hnorm
  let N : C(K, ℂ) × C(K, ℂ) → C(K, ℂ) × C(K, ℂ) :=
    fun u => ((u.1 a)⁻¹ • u.1, (u.1 a)⁻¹ • u.2)
  have hc : ContinuousAt N (f, d) := by
    have hi : ContinuousAt (fun u : C(K, ℂ) × C(K, ℂ) => (u.1 a)⁻¹) (f, d) :=
      ((continuous_eval_const a).comp continuous_fst).continuousAt.inv₀ (by simp [hf])
    exact (hi.smul continuous_fst.continuousAt).prodMk (hi.smul continuous_snd.continuousAt)
  obtain ⟨δ, hδ, hN⟩ := Metric.continuousAt_iff.mp hc ε hε
  obtain ⟨h, hh⟩ := exists_polynomial_modelG_C1_approx hr0 hr1 (lt_min hδ zero_lt_one)
  let u := h.toContinuousMapOn K
  let v := h.derivative.toContinuousMapOn K
  have huv : dist (u, v) (f, d) < δ := by
    rw [Prod.dist_eq, max_lt_iff]
    constructor
    · rw [dist_eq_norm, ContinuousMap.norm_lt_iff _ hδ]
      intro z
      exact ((hh z z.property).1).trans_le (min_le_left _ _)
    · rw [dist_eq_norm, ContinuousMap.norm_lt_iff _ hδ]
      intro z
      exact ((hh z z.property).2).trans_le (min_le_left _ _)
  have hzero : h.eval z0 ≠ 0 := by
    intro he
    have hlt := ((hh z0 z0_mem_K).1).trans_le (min_le_right _ _)
    simp [he, hnorm] at hlt
  have hnear : dist ((h.eval z0)⁻¹ • u) f < ε ∧
      dist ((h.eval z0)⁻¹ • v) d < ε := by
    simpa only [N, hf, inv_one, one_smul, Prod.dist_eq, max_lt_iff] using hN huv
  let g : ℂ[X] := C ((h.eval z0)⁻¹) * h
  refine ⟨g, by simp [g, hzero], fun z hz => ?_⟩
  have hvalue := (ContinuousMap.dist_apply_le_dist (⟨z, hz⟩ : K)).trans_lt hnear.1
  have hderiv := (ContinuousMap.dist_apply_le_dist (⟨z, hz⟩ : K)).trans_lt hnear.2
  constructor
  · simpa [g, u, f, dist_eq_norm] using hvalue
  · simpa [g, v, d, dist_eq_norm] using hderiv

/-- Transfer the three model conditions to an actual complex polynomial.
Compactness turns nonvanishing of `modelF'` and the strict boundary inequality
into uniform margins; normalized C¹ approximation preserves both margins. -/
theorem exists_base_polynomial {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hnorm : modelG r z0 = 1)
    (hderiv : ∀ z ∈ K, deriv (modelF r) z ≠ 0)
    (hboundary : ∀ z : ℂ, ‖q.eval z‖ = 1 → 1 < ‖modelG r z‖) :
    ∃ g : ℂ[X], g.eval z0 = 1 ∧
      (∀ z ∈ K, (basePolynomial g).derivative.eval z ≠ 0) ∧
      (∀ z : ℂ, ‖q.eval z‖ = 1 → 1 < ‖g.eval z‖) := by
  have hG := analyticOnNhd_modelG hr0.le hr1
  have hF := analyticOnNhd_modelF hr0.le hr1
  obtain ⟨a, ha, hmin⟩ := isCompact_K.exists_isMinOn ⟨z0, z0_mem_K⟩
    hF.deriv.continuousOn.norm
  have hμ : 0 < ‖deriv (modelF r) a‖ := norm_pos_iff.mpr (hderiv a ha)
  let B : Set ℂ := {z | ‖q.eval z‖ = 1}
  have hBK : B ⊆ K := fun _ hz => hz.le
  have hBc : IsCompact B := isCompact_K.of_isClosed_subset
    (isClosed_eq q.continuous.norm continuous_const) hBK
  obtain ⟨b, hb, hminB⟩ := hBc.exists_isMinOn ⟨1, q_one_norm⟩
    (hG.continuousOn.norm.mono hBK)
  have hlambda : 0 < ‖modelG r b‖ - 1 := sub_pos.mpr (hboundary b hb)
  obtain ⟨R, hR⟩ := isCompact_K.exists_bound_of_continuousOn
    (show ContinuousOn (fun z : ℂ => z - z0) K from
      (continuous_id.sub continuous_const).continuousOn)
  have hR0 : 0 ≤ R := by simpa using hR z0 z0_mem_K
  have hR1 : 0 < 1 + R := by positivity
  let ε : ℝ := min (‖deriv (modelF r) a‖ / (1 + R)) (‖modelG r b‖ - 1)
  have hε : 0 < ε := lt_min (div_pos hμ hR1) hlambda
  have hεμ : ε * (1 + R) ≤ ‖deriv (modelF r) a‖ :=
    (le_div_iff₀ hR1).mp (min_le_left _ _)
  have hεboundary : ε ≤ ‖modelG r b‖ - 1 := min_le_right _ _
  obtain ⟨g, hg0, hg⟩ := exists_normalized_polynomial_modelG_C1_approx hr0 hr1 hnorm hε
  have hfder : ∀ z ∈ K, deriv (modelF r) z =
      modelG r z + (z - z0) * deriv (modelG r) z := by
    intro z hz
    simpa only [modelF, id_eq, one_mul] using
      (((hasDerivAt_id z).sub_const z0).mul (hG z hz).differentiableAt.hasDerivAt).deriv
  refine ⟨g, hg0, ?_, ?_⟩
  · intro z hz
    have he : (basePolynomial g).derivative.eval z - deriv (modelF r) z =
        (g.eval z - modelG r z) +
          (z - z0) * (g.derivative.eval z - deriv (modelG r) z) := by
      rw [hfder z hz]
      simp only [basePolynomial, derivative_mul, derivative_sub, derivative_X, derivative_C,
        sub_zero, eval_add, eval_mul, one_mul, eval_sub, eval_X, eval_C]
      ring
    have hclose : ‖(basePolynomial g).derivative.eval z - deriv (modelF r) z‖ <
        ‖deriv (modelF r) a‖ := by
      rw [he]
      calc
        _ ≤ ‖g.eval z - modelG r z‖ +
            ‖(z - z0) * (g.derivative.eval z - deriv (modelG r) z)‖ := norm_add_le _ _
        _ < ε + R * ε := by
          apply add_lt_add_of_lt_of_le (hg z hz).1
          rw [norm_mul]
          exact mul_le_mul (hR z hz) (hg z hz).2.le (norm_nonneg _) hR0
        _ ≤ ‖deriv (modelF r) a‖ := by nlinarith only [hεμ]
    intro hzero
    have hlow := hmin hz
    simp only [hzero, zero_sub, norm_neg] at hclose
    exact (not_lt_of_ge hlow) hclose
  · intro z hz
    have hnormdiff := norm_sub_norm_le (modelG r z) (g.eval z)
    rw [norm_sub_rev] at hnormdiff
    have hclose := ((hg z (hBK hz)).1).trans_le hεboundary
    have hlow : ‖modelG r b‖ ≤ ‖modelG r z‖ := hminB hz
    linarith

end
end SmaleConstruction

/- ## Counterexample construction: PerturbationBounds -/

/-
# Bounds for the large-power perturbation

These elementary lemmas are independent of the analytic model.  In particular,
only `Defs` is imported.  All constants below are existential except for the
fixed quartic defining the lemniscate.
-/

namespace SmaleConstruction
namespace Perturbation

open Polynomial Complex Set Metric Filter
open scoped Topology BigOperators

noncomputable section

lemma radius_pos : 0 < radius := Real.sqrt_pos.2 (by norm_num)

lemma radius_sq : radius ^ 2 = 4097 := Real.sq_sqrt (by norm_num)

lemma radius_gt_64 : 64 < radius := by
  nlinarith [radius_sq, radius_pos]

lemma radius_lt_65 : radius < 65 := by
  nlinarith [radius_sq, radius_pos]

lemma radius_ne_zero : (radius : ℂ) ≠ 0 := by
  exact_mod_cast ne_of_gt radius_pos

lemma q_eval (z : ℂ) : q.eval z = (z ^ 4 + 64 * I) / radius := by
  simp [q, div_eq_mul_inv, mul_comm]

lemma q_eval_norm (z : ℂ) : ‖q.eval z‖ = ‖z ^ 4 + 64 * I‖ / radius := by
  rw [q_eval, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos radius_pos]

/-- The norm of the constant term of the defining quartic. -/
def tau : ℝ := 64 / radius

lemma tau_pos : 0 < tau := div_pos (by norm_num) radius_pos

lemma tau_lt_one : tau < 1 := by
  rw [tau, div_lt_one radius_pos]
  exact radius_gt_64

lemma q_zero_norm : ‖q.eval 0‖ = tau := by
  simp [q_eval_norm, tau]

lemma q_z0_norm_lt_tau : ‖q.eval z0‖ < tau := by
  have hs : Complex.normSq (z0 ^ 4 + 64 * I) < (64 : ℝ) ^ 2 := by
    norm_num [z0, Complex.normSq_apply, pow_succ, Complex.mul_re, Complex.mul_im]
  have hn : ‖z0 ^ 4 + 64 * I‖ < (64 : ℝ) := by
    rw [← Complex.sq_norm] at hs
    nlinarith [norm_nonneg (z0 ^ 4 + 64 * I)]
  rw [q_eval_norm]
  exact div_lt_div_of_pos_right hn radius_pos

lemma q_z0_norm_lt_one : ‖q.eval z0‖ < 1 := q_z0_norm_lt_tau.trans tau_lt_one

lemma z0_mem_K : z0 ∈ K := q_z0_norm_lt_one.le

lemma norm_pow_four_le (z : ℂ) : ‖z‖ ^ 4 ≤ radius * ‖q.eval z‖ + 64 := by
  calc
    ‖z‖ ^ 4 = ‖z ^ 4‖ := (norm_pow _ _).symm
    _ = ‖(z ^ 4 + 64 * I) - 64 * I‖ := by ring_nf
    _ ≤ ‖z ^ 4 + 64 * I‖ + ‖64 * I‖ := norm_sub_le _ _
    _ = radius * ‖q.eval z‖ + 64 := by
      rw [q_eval_norm, mul_div_cancel₀ _ (ne_of_gt radius_pos)]
      norm_num

lemma norm_lt_four {z : ℂ} (hz : ‖q.eval z‖ ≤ 2) : ‖z‖ < 4 := by
  have hp : ‖z‖ ^ 4 ≤ radius * 2 + 64 := by
    linarith [norm_pow_four_le z, mul_le_mul_of_nonneg_left hz radius_pos.le]
  by_contra h
  have h4 : (4 : ℝ) ^ 4 ≤ ‖z‖ ^ 4 :=
    pow_le_pow_left₀ (by norm_num) (le_of_not_gt h) 4
  linarith [radius_lt_65]

lemma isCompact_sublevel_two : IsCompact {z : ℂ | ‖q.eval z‖ ≤ 2} := by
  apply isCompact_iff_isClosed_bounded.mpr
  refine ⟨isClosed_le q.continuous.norm continuous_const, ?_⟩
  apply (isBounded_closedBall (x := (0 : ℂ)) (r := 4)).subset
  intro z hz
  simpa using (norm_lt_four hz).le

lemma isCompact_K : IsCompact K := by
  apply isCompact_sublevel_two.of_isClosed_subset
    (isClosed_le q.continuous.norm continuous_const)
  intro z hz
  exact (show ‖q.eval z‖ ≤ 1 from hz).trans (by norm_num)

lemma norm_le_q_growth (z : ℂ) : ‖z‖ ≤ 130 * max 1 ‖q.eval z‖ := by
  have ht : ‖z‖ ≤ ‖z‖ ^ 4 + 1 := by
    by_cases h : ‖z‖ ≤ 1
    · nlinarith [pow_nonneg (norm_nonneg z) 4]
    · have h1 : 1 ≤ ‖z‖ := le_of_not_ge h
      have hh : ‖z‖ ≤ ‖z‖ ^ 4 := by
        simpa using (pow_le_pow_right₀ h1 (show 1 ≤ 4 by norm_num))
      linarith
  have hR : 1 ≤ max 1 ‖q.eval z‖ := le_max_left _ _
  have hr : ‖q.eval z‖ ≤ max 1 ‖q.eval z‖ := le_max_right _ _
  have hb : radius * ‖q.eval z‖ ≤ 65 * max 1 ‖q.eval z‖ :=
    mul_le_mul radius_lt_65.le hr (norm_nonneg _) (by norm_num)
  linarith [norm_pow_four_le z]

/-- A global coefficient bound measured by the quartic, not merely by `‖z‖`.
This bound is valid throughout the unbounded exterior of the lemniscate. -/
lemma polynomial_growth (p : ℂ[X]) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      ‖p.eval z‖ ≤ C * max 1 ‖q.eval z‖ ^ p.natDegree := by
  let C : ℝ := ∑ k ∈ Finset.range (p.natDegree + 1), ‖p.coeff k‖ * 130 ^ k
  have hC : 0 ≤ C := Finset.sum_nonneg fun k _ => mul_nonneg (norm_nonneg _) (by positivity)
  refine ⟨C + 1, by positivity, fun z => ?_⟩
  have hR : 1 ≤ max 1 ‖q.eval z‖ := le_max_left _ _
  calc
    ‖p.eval z‖ = ‖∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * z ^ k‖ := by
      rw [Polynomial.eval_eq_sum_range]
    _ ≤ ∑ k ∈ Finset.range (p.natDegree + 1), ‖p.coeff k * z ^ k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (p.natDegree + 1),
        (‖p.coeff k‖ * 130 ^ k) * max 1 ‖q.eval z‖ ^ p.natDegree := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' : k ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      calc
        ‖p.coeff k * z ^ k‖ = ‖p.coeff k‖ * ‖z‖ ^ k := by rw [norm_mul, norm_pow]
        _ ≤ ‖p.coeff k‖ * (130 * max 1 ‖q.eval z‖) ^ k :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) (norm_le_q_growth z) k)
            (norm_nonneg _)
        _ = (‖p.coeff k‖ * 130 ^ k) * max 1 ‖q.eval z‖ ^ k := by rw [mul_pow]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR hk') (by positivity)
    _ = C * max 1 ‖q.eval z‖ ^ p.natDegree := by rw [Finset.sum_mul]
    _ ≤ (C + 1) * max 1 ‖q.eval z‖ ^ p.natDegree := by gcongr; linarith

/-- A positive continuous function has a positive uniform lower bound on `K`. -/
lemma derivative_lower_bound (p : ℂ[X]) (hp : ∀ z ∈ K, p.derivative.eval z ≠ 0) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ z ∈ K, μ ≤ ‖p.derivative.eval z‖ := by
  exact isCompact_K.exists_forall_le' p.derivative.continuous.norm.continuousOn
    (fun z hz => norm_pos_iff.mpr (hp z hz))

/-- Compactness turns a strict boundary inequality into an inequality on a
whole fixed collar.  The collar is above `tau`, below level two, and is
separated from the anchoring point. -/
lemma good_collar (g : ℂ[X])
    (hg : ∀ z : ℂ, ‖q.eval z‖ = 1 → 1 < ‖g.eval z‖) :
    ∃ σ δ η : ℝ, 0 < σ ∧ σ < 1 ∧ tau < 1 - σ ∧
      0 < δ ∧ 0 < η ∧
      ∀ z : ℂ, 1 - σ ≤ ‖q.eval z‖ → ‖q.eval z‖ ≤ 1 + σ →
        1 + δ < ‖g.eval z‖ ∧ η ≤ ‖z - z0‖ := by
  let B : Set ℂ := {z | ‖q.eval z‖ = 1}
  have hB : IsCompact B := isCompact_sublevel_two.of_isClosed_subset
    (isClosed_eq q.continuous.norm continuous_const)
    (fun z hz => by change ‖q.eval z‖ = 1 at hz; simp [hz])
  obtain ⟨b, hb, hbg⟩ := hB.exists_forall_le' g.continuous.norm.continuousOn hg
  let δ : ℝ := (b - 1) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδb : 1 + δ < b := by dsimp [δ]; linarith
  let D : Set ℂ := {z | ‖q.eval z‖ ≤ 2 ∧ ‖g.eval z‖ ≤ 1 + δ}
  have hD : IsCompact D := isCompact_sublevel_two.inter_right
    (isClosed_le g.continuous.norm continuous_const)
  obtain ⟨e, he, heD⟩ := hD.exists_forall_le'
    ((q.continuous.norm.sub continuous_const).abs.continuousOn)
    (a := 0) (fun z hz => by
      apply abs_pos.mpr
      intro h
      have hzB : z ∈ B := sub_eq_zero.mp h
      have := hbg z hzB
      exact (not_lt_of_ge (le_trans this hz.2)) hδb)
  obtain ⟨σ, hσ, hσsmall⟩ := exists_between
    (lt_min he (sub_pos.mpr tau_lt_one))
  have hστ : σ < 1 - tau := hσsmall.trans_le (min_le_right _ _)
  have hσ1 : σ < 1 := by linarith [tau_pos]
  have hcollar : ∀ z : ℂ, 1 - σ ≤ ‖q.eval z‖ → ‖q.eval z‖ ≤ 1 + σ →
      1 + δ < ‖g.eval z‖ := by
    intro z hz1 hz2
    by_contra h
    have hzD : z ∈ D := ⟨by linarith, le_of_not_gt h⟩
    have hh : |‖q.eval z‖ - 1| ≤ σ := abs_le.mpr ⟨by linarith, by linarith⟩
    have := heD z hzD
    have := hσsmall.trans_le (min_le_left _ _)
    linarith
  let L : Set ℂ := {z | 1 - σ ≤ ‖q.eval z‖ ∧ ‖q.eval z‖ ≤ 1 + σ}
  have hL : IsCompact L := isCompact_sublevel_two.of_isClosed_subset
    ((isClosed_le continuous_const q.continuous.norm).inter
      (isClosed_le q.continuous.norm continuous_const))
    (fun z hz => by
      change _ ∧ _ at hz
      change ‖q.eval z‖ ≤ 2
      linarith [hz.2])
  obtain ⟨η, hη, hηL⟩ := hL.exists_forall_le'
    ((continuous_id.sub continuous_const).norm.continuousOn)
    (a := 0) (fun z hz => by
      apply norm_pos_iff.mpr
      intro heq
      have heq' : z = z0 := sub_eq_zero.mp heq
      rw [heq'] at hz
      have := q_z0_norm_lt_tau
      have := hz.1
      linarith)
  exact ⟨σ, δ, η, hσ, hσ1, by linarith, hδ, hη,
    fun z hz1 hz2 => ⟨hcollar z hz1 hz2, hηL z ⟨hz1, hz2⟩⟩⟩

lemma derivative_upper_bound (p : ℂ[X]) :
    ∃ V : ℝ, 0 < V ∧ ∀ z : ℂ, ‖q.eval z‖ ≤ 2 → ‖p.derivative.eval z‖ ≤ V := by
  obtain ⟨V, hV⟩ := isCompact_sublevel_two.exists_bound_of_continuousOn
    p.derivative.continuous.continuousOn
  refine ⟨max 1 V, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun z hz => ?_⟩
  exact (hV z hz).trans (le_max_right _ _)

end
end Perturbation
end SmaleConstruction

/- ## Counterexample construction: PerturbationPrimitive -/

/-
# Finite primitives and radial estimates

The primitive is an explicit finite binomial sum.  Its straight-segment
integral formula is deduced from its polynomial derivative, not from a
primitive-existence theorem.  The estimate outside level `tau` is useful on
the moving critical set; no convergence on an exterior collar is asserted.
-/

namespace SmaleConstruction
namespace Perturbation

open Polynomial Complex Set Metric Filter MeasureTheory
open scoped Topology BigOperators

noncomputable section

/-- The primitive of `q^m` that vanishes at the center of the radial segments. -/
def radialPrimitive (m : ℕ) : ℂ[X] :=
  C ((radius : ℂ)⁻¹ ^ m) * ∑ k ∈ Finset.range (m + 1),
    C ((Nat.choose m k : ℂ) * (64 * I) ^ (m - k) / ((4 * k + 1 : ℕ) : ℂ)) *
      X ^ (4 * k + 1)

lemma derivative_primitive_term (a : ℂ) (k : ℕ) :
    (C (a / ((k + 1 : ℕ) : ℂ)) * X ^ (k + 1)).derivative = C a * X ^ k := by
  have hk : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  rw [derivative_C_mul, derivative_X_pow]
  simp only [Nat.add_sub_cancel]
  rw [← mul_assoc, ← C_mul, div_mul_cancel₀ _ hk]

lemma derivative_radialPrimitive (m : ℕ) : (radialPrimitive m).derivative = q ^ m := by
  unfold radialPrimitive q
  rw [derivative_C_mul, derivative_sum, mul_pow, ← C_pow, add_pow]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [derivative_primitive_term]
  simp [pow_mul, mul_comm, mul_left_comm]
  left
  simp only [← pow_mul, Nat.mul_comm]

@[simp] lemma radialPrimitive_zero (m : ℕ) : (radialPrimitive m).eval 0 = 0 := by
  simp [radialPrimitive, Polynomial.eval_finset_sum]

/-- The perturbation primitive is anchored at `z0`, not at the radial center. -/
def anchoredPrimitive (m : ℕ) : ℂ[X] :=
  radialPrimitive m - C ((radialPrimitive m).eval z0)

@[simp] lemma anchoredPrimitive_eval (m : ℕ) : (anchoredPrimitive m).eval z0 = 0 := by
  simp [anchoredPrimitive]

@[simp] lemma derivative_anchoredPrimitive (m : ℕ) :
    (anchoredPrimitive m).derivative = q ^ m := by
  simp [anchoredPrimitive, derivative_radialPrimitive]

lemma radialPrimitive_segment (m : ℕ) (z : ℂ) :
    (radialPrimitive m).eval z = z * ∫ t : ℝ in 0..1, q.eval ((t : ℂ) * z) ^ m := by
  have hd : ∀ t : ℝ,
      HasDerivAt (fun t : ℝ => (radialPrimitive m).eval ((t : ℂ) * z))
        (z * q.eval ((t : ℂ) * z) ^ m) t := by
    intro t
    have h := ((radialPrimitive m).hasDerivAt ((t : ℂ) * z)).comp (t : ℂ)
      ((hasDerivAt_id (t : ℂ)).mul_const z)
    simpa [derivative_radialPrimitive, mul_comm] using h.comp_ofReal
  have hi : IntervalIntegrable (fun t : ℝ => z * q.eval ((t : ℂ) * z) ^ m) volume 0 1 :=
    (continuous_const.mul ((q.continuous.comp
      (Complex.continuous_ofReal.mul continuous_const)).pow m)).intervalIntegrable 0 1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  simpa [intervalIntegral.integral_const_mul] using h.symm

lemma q_eval_real_mul (t : ℝ) (z : ℂ) :
    q.eval ((t : ℂ) * z) = (t : ℂ) ^ 4 * q.eval z + (1 - (t : ℂ) ^ 4) * q.eval 0 := by
  simp only [q_eval, zero_pow (by norm_num : 4 ≠ 0), zero_add]
  ring

lemma radial_norm_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (z : ℂ) :
    ‖q.eval ((t : ℂ) * z)‖ ≤ t ^ 4 * ‖q.eval z‖ + (1 - t ^ 4) * tau := by
  have ht40 : 0 ≤ t ^ 4 := pow_nonneg ht0 _
  have ht41 : t ^ 4 ≤ 1 := pow_le_one₀ ht0 ht1
  rw [q_eval_real_mul]
  calc
    _ ≤ ‖(t : ℂ) ^ 4 * q.eval z‖ + ‖(1 - (t : ℂ) ^ 4) * q.eval 0‖ := norm_add_le _ _
    _ = _ := by
      rw [norm_mul, norm_mul, ← Complex.ofReal_pow,
        ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ht40,
        abs_of_nonneg (sub_nonneg.mpr ht41), q_zero_norm]

lemma radial_norm_le_linear {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {z : ℂ} (hz : tau ≤ ‖q.eval z‖) :
    ‖q.eval ((t : ℂ) * z)‖ ≤ tau + (‖q.eval z‖ - tau) * t := by
  have ht4 : t ^ 4 ≤ t := by
    simpa [pow_succ] using mul_le_mul_of_nonneg_right (pow_le_one₀ ht0 ht1 (n := 3)) ht0
  have h := mul_le_mul_of_nonneg_left ht4 (sub_nonneg.mpr hz)
  linarith [radial_norm_le ht0 ht1 z]

lemma radial_norm_le_tau {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {z : ℂ} (hz : ‖q.eval z‖ ≤ tau) : ‖q.eval ((t : ℂ) * z)‖ ≤ tau := by
  have h := mul_le_mul_of_nonneg_left hz (pow_nonneg ht0 4)
  linarith [radial_norm_le ht0 ht1 z]

/-- The elementary real integral responsible for the factor `1/(m+1)`. -/
lemma integral_affine_pow (a b : ℝ) (hab : a < b) (m : ℕ) :
    (∫ t : ℝ in 0..1, (a + (b - a) * t) ^ m) =
      (b ^ (m + 1) - a ^ (m + 1)) / (((m : ℝ) + 1) * (b - a)) := by
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  have hd : ∀ t : ℝ,
      HasDerivAt (fun t : ℝ => (a + (b - a) * t) ^ (m + 1) /
        (((m : ℝ) + 1) * (b - a))) ((a + (b - a) * t) ^ m) t := by
    intro t
    convert (((((hasDerivAt_id t).const_mul (b - a)).const_add a).pow (m + 1)).div_const
      (((m : ℝ) + 1) * (b - a))) using 1
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, id, mul_one]
    field_simp
  have hi : IntervalIntegrable (fun t : ℝ => (a + (b - a) * t) ^ m) volume 0 1 :=
    (continuous_const.add (continuous_const.mul continuous_id)).pow m |>.intervalIntegrable 0 1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  simpa [sub_div] using h

/-- Exact `O(1/m)` radial bound when the endpoint is above level `tau`. -/
lemma radialPrimitive_norm_le (m : ℕ) {z : ℂ} (hz : tau < ‖q.eval z‖) :
    ‖(radialPrimitive m).eval z‖ ≤
      ‖z‖ * ‖q.eval z‖ ^ (m + 1) / (((m : ℝ) + 1) * (‖q.eval z‖ - tau)) := by
  have hc : Continuous (fun t : ℝ => q.eval ((t : ℂ) * z) ^ m) :=
    (q.continuous.comp (Complex.continuous_ofReal.mul continuous_const)).pow m
  have hr : Continuous (fun t : ℝ => (tau + (‖q.eval z‖ - tau) * t) ^ m) :=
    (continuous_const.add (continuous_const.mul continuous_id)).pow m
  have hi : (∫ t : ℝ in 0..1, ‖q.eval ((t : ℂ) * z) ^ m‖) ≤
      ∫ t : ℝ in 0..1, (tau + (‖q.eval z‖ - tau) * t) ^ m := by
    apply intervalIntegral.integral_mono_on (by norm_num) (hc.norm.intervalIntegrable _ _)
      (hr.intervalIntegrable _ _)
    intro t ht
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (radial_norm_le_linear ht.1 ht.2 hz.le) m
  rw [integral_affine_pow tau _ hz m] at hi
  rw [radialPrimitive_segment, norm_mul]
  calc
    _ ≤ ‖z‖ * (∫ t : ℝ in 0..1, ‖q.eval ((t : ℂ) * z) ^ m‖) :=
      mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_integral_norm (by norm_num))
        (norm_nonneg z)
    _ ≤ ‖z‖ * ((‖q.eval z‖ ^ (m + 1) - tau ^ (m + 1)) /
        (((m : ℝ) + 1) * (‖q.eval z‖ - tau))) :=
      mul_le_mul_of_nonneg_left hi (norm_nonneg z)
    _ ≤ ‖z‖ * (‖q.eval z‖ ^ (m + 1) /
        (((m : ℝ) + 1) * (‖q.eval z‖ - tau))) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg z)
      exact div_le_div_of_nonneg_right (sub_le_self _ (pow_nonneg tau_pos.le _))
        (mul_nonneg (by positivity) (sub_nonneg.mpr hz.le))
    _ = _ := (mul_div_assoc _ _ _).symm

lemma radialPrimitive_norm_le_tau (m : ℕ) {z : ℂ} (hz : ‖q.eval z‖ ≤ tau) :
    ‖(radialPrimitive m).eval z‖ ≤ ‖z‖ * tau ^ m := by
  rw [radialPrimitive_segment, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg z)
  have h : ‖∫ t : ℝ in 0..1, q.eval ((t : ℂ) * z) ^ m‖ ≤ tau ^ m * |(1 : ℝ) - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (radial_norm_le_tau ht.1.le ht.2 hz) m
  simpa using h

lemma anchoredPrimitive_norm_le (m : ℕ) {z : ℂ} (hz : tau < ‖q.eval z‖) :
    ‖(anchoredPrimitive m).eval z‖ ≤
      ‖z‖ * ‖q.eval z‖ ^ (m + 1) / (((m : ℝ) + 1) * (‖q.eval z‖ - tau)) +
        ‖z0‖ * tau ^ m := by
  calc
    _ = ‖(radialPrimitive m).eval z - (radialPrimitive m).eval z0‖ := by
      simp [anchoredPrimitive]
    _ ≤ ‖(radialPrimitive m).eval z‖ + ‖(radialPrimitive m).eval z0‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add (radialPrimitive_norm_le m hz)
      (radialPrimitive_norm_le_tau m q_z0_norm_lt_tau.le)

end
end Perturbation
end SmaleConstruction

/- ## Counterexample construction: PerturbationCritical -/

/-
# Control of the entire critical set

The derivative is an additive perturbation `p' + q^(2*n)`.  A global polynomial
bound excludes the whole unbounded exterior, and a compact positive lower
bound excludes the inner sublevel.  The primitive estimate is then applied
only at critical points, where its otherwise growing numerator is bounded.
-/

namespace SmaleConstruction
namespace Perturbation

open Polynomial Complex Set Metric Filter
open scoped Topology BigOperators

noncomputable section

/-- The unnormalized additive perturbation. -/
def perturbedPolynomial (p : ℂ[X]) (n : ℕ) : ℂ[X] :=
  p + anchoredPrimitive (2 * n)

@[simp] lemma derivative_perturbedPolynomial (p : ℂ[X]) (n : ℕ) :
    (perturbedPolynomial p n).derivative = p.derivative + q ^ (2 * n) := by
  simp [perturbedPolynomial]

@[simp] lemma perturbedPolynomial_eval_z0 (p : ℂ[X]) (n : ℕ) :
    (perturbedPolynomial p n).eval z0 = p.eval z0 := by
  simp [perturbedPolynomial]

lemma critical_norm_eq (p : ℂ[X]) (n : ℕ) {z : ℂ}
    (hz : (perturbedPolynomial p n).derivative.eval z = 0) :
    ‖q.eval z‖ ^ (2 * n) = ‖p.derivative.eval z‖ := by
  have h : p.derivative.eval z + q.eval z ^ (2 * n) = 0 := by simpa using hz
  have hq := eq_neg_of_add_eq_zero_right h
  rw [← norm_pow, hq, norm_neg]

lemma even_pow_tendsto_zero {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    Tendsto (fun n : ℕ => a ^ (2 * n)) atTop (𝓝 0) := by
  simpa only [pow_mul] using tendsto_pow_atTop_nhds_zero_of_lt_one
    (pow_nonneg ha0 2) (pow_lt_one₀ ha0 ha1 (by norm_num : 2 ≠ 0))

/-- Simultaneous localization of **all** complex critical points. -/
lemma eventually_critical_in_collar (p : ℂ[X])
    (hp : ∀ z ∈ K, p.derivative.eval z ≠ 0)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ z : ℂ,
      (perturbedPolynomial p n).derivative.eval z = 0 →
        1 - σ < ‖q.eval z‖ ∧ ‖q.eval z‖ < 1 + σ := by
  obtain ⟨μ, hμ, hμp⟩ := derivative_lower_bound p hp
  obtain ⟨C, hC, hCp⟩ := polynomial_growth p.derivative
  have hin : ∀ᶠ n : ℕ in atTop, (1 - σ) ^ (2 * n) < μ :=
    (even_pow_tendsto_zero (by linarith) (by linarith)).eventually_lt_const hμ
  have hout : ∀ᶠ n : ℕ in atTop, C < (1 + σ) ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt (by linarith : 1 < 1 + σ)).eventually
      (eventually_gt_atTop C)
  filter_upwards [hin, hout, eventually_ge_atTop p.derivative.natDegree] with n hni hno hnd
  intro z hz
  have hcrit := critical_norm_eq p n hz
  constructor
  · by_contra h
    have hR : ‖q.eval z‖ ≤ 1 - σ := le_of_not_gt h
    have hzK : z ∈ K := by change ‖q.eval z‖ ≤ 1; linarith
    have hpow := pow_le_pow_left₀ (norm_nonneg _) hR (2 * n)
    have hmin := hμp z hzK
    linarith
  · by_contra h
    have hR : 1 + σ ≤ ‖q.eval z‖ := le_of_not_gt h
    have hR1 : 1 ≤ ‖q.eval z‖ := by linarith
    have hR0 : 0 < ‖q.eval z‖ := by linarith
    have hgrowth := hCp z
    rw [max_eq_right hR1] at hgrowth
    have hh : C * ‖q.eval z‖ ^ p.derivative.natDegree < ‖q.eval z‖ ^ (2 * n) := by
      calc
        _ < (1 + σ) ^ n * ‖q.eval z‖ ^ p.derivative.natDegree :=
          mul_lt_mul_of_pos_right hno (pow_pos hR0 _)
        _ ≤ ‖q.eval z‖ ^ n * ‖q.eval z‖ ^ n :=
          mul_le_mul (pow_le_pow_left₀ (by linarith) hR n)
            (pow_le_pow_right₀ hR1 hnd) (pow_nonneg (norm_nonneg _) _) (by positivity)
        _ = _ := by rw [two_mul, pow_add]
    linarith

/-- A uniform explicit upper bound for the anchored primitive at a critical
point in a fixed collar.  Unlike a bound on a fixed exterior collar, this
bound tends to zero. -/
lemma critical_primitive_bound (p : ℂ[X]) (n : ℕ)
    {σ V : ℝ} (hσ1 : σ < 1) (hστ : tau < 1 - σ) (hV : 0 < V)
    {z : ℂ} (hz : (perturbedPolynomial p n).derivative.eval z = 0)
    (hz1 : 1 - σ ≤ ‖q.eval z‖) (hz2 : ‖q.eval z‖ ≤ 1 + σ)
    (hzV : ‖p.derivative.eval z‖ ≤ V) :
    ‖(anchoredPrimitive (2 * n)).eval z‖ ≤
      (8 * V / (1 - σ - tau)) * (1 / ((n : ℝ) + 1)) + ‖z0‖ * tau ^ (2 * n) := by
  have hzτ : tau < ‖q.eval z‖ := hστ.trans_le hz1
  have hz2' : ‖q.eval z‖ ≤ 2 := by linarith
  have hzn : ‖z‖ ≤ 4 := (norm_lt_four hz2').le
  have hgap : 0 < 1 - σ - tau := by linarith
  have hpow : ‖q.eval z‖ ^ (2 * n) ≤ V := (critical_norm_eq p n hz).trans_le hzV
  have hnum : ‖z‖ * ‖q.eval z‖ ^ (2 * n + 1) ≤ 8 * V := by
    rw [pow_succ]
    calc
      _ ≤ 4 * (V * 2) :=
        mul_le_mul hzn
          (mul_le_mul hpow hz2' (norm_nonneg _) hV.le)
          (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)) (by norm_num)
      _ = _ := by ring
  have hden : ((n : ℝ) + 1) * (1 - σ - tau) ≤
      (((2 * n : ℕ) : ℝ) + 1) * (‖q.eval z‖ - tau) := by
    apply mul_le_mul
    · norm_num
      linarith [Nat.cast_nonneg (α := ℝ) n]
    · linarith
    · exact hgap.le
    · positivity
  have hdiv := div_le_div₀ (by positivity : 0 ≤ 8 * V) hnum
    (mul_pos (by positivity) hgap) hden
  have heq : (8 * V) / (((n : ℝ) + 1) * (1 - σ - tau)) =
      (8 * V / (1 - σ - tau)) * (1 / ((n : ℝ) + 1)) := by
    simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
    ring
  rw [heq] at hdiv
  exact (anchoredPrimitive_norm_le (2 * n) hzτ).trans (add_le_add hdiv le_rfl)

/-- The entire moving critical set has a small primitive quotient, for every
sufficiently large exponent.  The exponent is deliberately not specified. -/
lemma eventually_critical_control (p : ℂ[X])
    (hp : ∀ z ∈ K, p.derivative.eval z ≠ 0)
    {σ η ε : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hστ : tau < 1 - σ)
    (hη : 0 < η) (hε : 0 < ε)
    (hdist : ∀ z : ℂ, 1 - σ ≤ ‖q.eval z‖ → ‖q.eval z‖ ≤ 1 + σ → η ≤ ‖z - z0‖) :
    ∀ᶠ n : ℕ in atTop, ∀ z : ℂ,
      (perturbedPolynomial p n).derivative.eval z = 0 →
        1 - σ < ‖q.eval z‖ ∧ ‖q.eval z‖ < 1 + σ ∧
          ‖(anchoredPrimitive (2 * n)).eval z / (z - z0)‖ < ε := by
  obtain ⟨V, hV, hVp⟩ := derivative_upper_bound p
  let E : ℕ → ℝ := fun n =>
    (8 * V / (1 - σ - tau)) * (1 / ((n : ℝ) + 1)) + ‖z0‖ * tau ^ (2 * n)
  have hE : Tendsto E atTop (𝓝 0) := by
    simpa only [mul_zero, zero_add] using
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (8 * V / (1 - σ - tau))).add
        ((even_pow_tendsto_zero tau_pos.le tau_lt_one).const_mul ‖z0‖)
  have hsmall : ∀ᶠ n : ℕ in atTop, E n < ε * η := hE.eventually_lt_const (mul_pos hε hη)
  filter_upwards [eventually_critical_in_collar p hp hσ0 hσ1, hsmall] with n hn hEn
  intro z hz
  obtain ⟨hz1, hz2⟩ := hn z hz
  have hzd := hdist z hz1.le hz2.le
  have hz2' : ‖q.eval z‖ ≤ 2 := by linarith
  have hb := critical_primitive_bound p n hσ1 hστ hV hz hz1.le hz2.le (hVp z hz2')
  refine ⟨hz1, hz2, ?_⟩
  rw [norm_div, div_lt_iff₀ (hη.trans_le hzd)]
  exact (hb.trans_lt hEn).trans_le (mul_le_mul_of_nonneg_left hzd hε.le)

lemma q_natDegree : q.natDegree = 4 := by
  rw [q, natDegree_C_mul (inv_ne_zero radius_ne_zero), natDegree_X_pow_add_C]

lemma two_le_natDegree_perturbedPolynomial (p : ℂ[X]) {n : ℕ}
    (hpn : p.derivative.natDegree < 8 * n) :
    2 ≤ (perturbedPolynomial p n).natDegree := by
  have hq : (q ^ (2 * n)).natDegree = 8 * n := by rw [natDegree_pow, q_natDegree]; omega
  have hd : (perturbedPolynomial p n).derivative.natDegree = 8 * n := by
    rw [derivative_perturbedPolynomial,
      natDegree_add_eq_right_of_natDegree_lt (hpn.trans_eq hq.symm), hq]
  have h := natDegree_derivative_le (perturbedPolynomial p n)
  rw [hd] at h
  omega

lemma eventually_two_le_natDegree (p : ℂ[X]) :
    ∀ᶠ n : ℕ in atTop, 2 ≤ (perturbedPolynomial p n).natDegree := by
  filter_upwards [eventually_gt_atTop p.derivative.natDegree] with n hn
  apply two_le_natDegree_perturbedPolynomial p
  omega

end
end Perturbation
end SmaleConstruction

/- ## Counterexample construction: Perturbation -/

/-
# The final polynomial construction

Given a polynomial `g` with value one at `z0`, with `(X-C z0)*g` having no
critical points on `K`, and with `‖g‖ > 1` on `‖q‖ = 1`, we construct an
`AllBadWitness`.  The perturbation is the finite polynomial primitive of
`q^(2*n)`, anchored at `z0`, for an existential sufficiently large `n`.

There are no analytic-model assumptions hidden in this module: the three
conditions on `g` are explicit hypotheses of the final theorem.  No root
counting, Rouché theorem, or assumption about the location of pre-existing
critical points is used.
-/

namespace SmaleConstruction

open Polynomial Complex Set Metric Filter
open scoped Topology

noncomputable section

namespace Perturbation

/-- Translation followed by normalization of the derivative at the base point. -/
def normalizeAt (p : ℂ[X]) (a : ℂ) : ℂ[X] :=
  C ((p.derivative.eval a)⁻¹) * p.comp (X + C a)

lemma normalizeAt_eval (p : ℂ[X]) (a z : ℂ) :
    (normalizeAt p a).eval z = (p.derivative.eval a)⁻¹ * p.eval (z + a) := by
  simp [normalizeAt, Polynomial.eval_comp]

lemma normalizeAt_derivative_eval (p : ℂ[X]) (a z : ℂ) :
    (normalizeAt p a).derivative.eval z =
      (p.derivative.eval a)⁻¹ * p.derivative.eval (z + a) := by
  simp [normalizeAt, derivative_comp, Polynomial.eval_comp]

lemma normalizeAt_natDegree (p : ℂ[X]) (a : ℂ) (ha : p.derivative.eval a ≠ 0) :
    (normalizeAt p a).natDegree = p.natDegree := by
  rw [normalizeAt, natDegree_C_mul (inv_ne_zero ha), natDegree_comp, natDegree_X_add_C, mul_one]

/-- A purely algebraic normalization lemma, also valid at base points other
than the fixed `z0`. -/
lemma allBadWitness_normalizeAt (p : ℂ[X]) (a : ℂ)
    (hp0 : p.eval a = 0) (hp1 : p.derivative.eval a ≠ 0) (hdeg : 2 ≤ p.natDegree)
    (hcrit : ∀ z : ℂ, p.derivative.eval z = 0 →
      ‖p.derivative.eval a‖ < ‖p.eval z / (z - a)‖) :
    AllBadWitness (normalizeAt p a) := by
  have hdeg' : 2 ≤ (normalizeAt p a).natDegree := by
    rwa [normalizeAt_natDegree p a hp1]
  have hnz : normalizeAt p a ≠ 0 := by
    intro h
    simp [h] at hdeg'
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [degree_eq_natDegree hnz]
    exact_mod_cast hdeg'
  · simp [normalizeAt_eval, hp0]
  · simp [normalizeAt_derivative_eval, hp1]
  · intro c hc
    have hc' : p.derivative.eval (c + a) = 0 := by
      rw [normalizeAt_derivative_eval] at hc
      exact (mul_eq_zero.mp hc).resolve_left (inv_ne_zero hp1)
    have hratio : ‖(normalizeAt p a).eval c / c‖ =
        ‖p.eval (c + a) / (c + a - a)‖ / ‖p.derivative.eval a‖ := by
      simp only [normalizeAt_eval, add_sub_cancel_right, norm_mul, norm_inv,
        div_eq_mul_inv]
      ring
    rw [hratio, one_lt_div₀ (norm_pos_iff.mpr hp1)]
    exact hcrit (c + a) hc'

/-- The normalizing scalar, independent of the particular normalized `g`. -/
def normalizingScalar (n : ℕ) : ℂ := 1 + q.eval z0 ^ (2 * n)

lemma base_derivative_eval_z0 (g : ℂ[X]) (hg : g.eval z0 = 1) :
    (basePolynomial g).derivative.eval z0 = 1 := by
  simp [basePolynomial, hg]

lemma perturbed_base_derivative_eval_z0 (g : ℂ[X]) (hg : g.eval z0 = 1) (n : ℕ) :
    (perturbedPolynomial (basePolynomial g) n).derivative.eval z0 = normalizingScalar n := by
  simp [base_derivative_eval_z0 g hg, normalizingScalar]

lemma eventually_normalizingScalar {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, normalizingScalar n ≠ 0 ∧ ‖normalizingScalar n‖ < 1 + ε := by
  have hsmall : ∀ᶠ n : ℕ in atTop, ‖q.eval z0‖ ^ (2 * n) < min 1 ε :=
    (even_pow_tendsto_zero (norm_nonneg _) q_z0_norm_lt_one).eventually_lt_const
      (lt_min zero_lt_one hε)
  filter_upwards [hsmall] with n hn
  obtain ⟨hn1, hnε⟩ := lt_min_iff.mp hn
  constructor
  · intro h
    have hh : q.eval z0 ^ (2 * n) = -1 := eq_neg_of_add_eq_zero_right h
    have hh' : ‖q.eval z0‖ ^ (2 * n) = 1 := by rw [← norm_pow, hh, norm_neg, norm_one]
    linarith
  · have h := norm_add_le (1 : ℂ) (q.eval z0 ^ (2 * n))
    rw [norm_one, norm_pow] at h
    change ‖1 + q.eval z0 ^ (2 * n)‖ < 1 + ε
    linarith

end Perturbation

/-- A finite polynomial family.  The final theorem chooses an existential
large index; there is no prescribed enormous integer in the construction. -/
def perturbationWitness (g : ℂ[X]) (n : ℕ) : ℂ[X] :=
  Perturbation.normalizeAt (Perturbation.perturbedPolynomial (basePolynomial g) n) z0

/-- The explicit primitive-and-normalization formula for the witness family. -/
lemma perturbationWitness_formula (g : ℂ[X]) (hg : g.eval z0 = 1) (n : ℕ) :
    perturbationWitness g n =
      C ((1 + q.eval z0 ^ (2 * n))⁻¹) *
        (basePolynomial g + Perturbation.anchoredPrimitive (2 * n)).comp (X + C z0) := by
  unfold perturbationWitness Perturbation.normalizeAt
  rw [Perturbation.perturbed_base_derivative_eval_z0 g hg n]
  rfl

/-- Every sufficiently large member of the perturbation family is an
`AllBadWitness`.  In particular the argument controls all critical points,
including any distant ones, rather than just those in a bounded region. -/
theorem eventually_allBadWitness_perturbation (g : ℂ[X])
    (hg0 : g.eval z0 = 1)
    (hderiv : ∀ z ∈ K, (basePolynomial g).derivative.eval z ≠ 0)
    (hboundary : ∀ z : ℂ, ‖q.eval z‖ = 1 → 1 < ‖g.eval z‖) :
    ∀ᶠ n : ℕ in atTop, AllBadWitness (perturbationWitness g n) := by
  obtain ⟨σ, δ, η, hσ0, hσ1, hστ, hδ, hη, hgood⟩ :=
    Perturbation.good_collar g hboundary
  have hε : 0 < δ / 2 := by positivity
  have hcontrol := Perturbation.eventually_critical_control (basePolynomial g) hderiv
    hσ0 hσ1 hστ hη hε (fun z hz1 hz2 => (hgood z hz1 hz2).2)
  filter_upwards [hcontrol, Perturbation.eventually_normalizingScalar hε,
    Perturbation.eventually_two_le_natDegree (basePolynomial g)] with n hn hAn hdegree
  have hp0 : (Perturbation.perturbedPolynomial (basePolynomial g) n).eval z0 = 0 := by
    simp [basePolynomial]
  have hp1 := Perturbation.perturbed_base_derivative_eval_z0 g hg0 n
  apply Perturbation.allBadWitness_normalizeAt _ _ hp0 (by rw [hp1]; exact hAn.1) hdegree
  intro z hz
  obtain ⟨hz1, hz2, hzH⟩ := hn z hz
  obtain ⟨hzg, hzd⟩ := hgood z hz1.le hz2.le
  have hzne : z - z0 ≠ 0 := norm_pos_iff.mp (hη.trans_le hzd)
  have hratio : (Perturbation.perturbedPolynomial (basePolynomial g) n).eval z / (z - z0) =
      g.eval z + (Perturbation.anchoredPrimitive (2 * n)).eval z / (z - z0) := by
    simp only [Perturbation.perturbedPolynomial, basePolynomial, eval_add, eval_mul,
      eval_sub, eval_X, eval_C, add_div, mul_div_cancel_left₀ _ hzne]
  have hnorm : ‖g.eval z‖ - ‖(Perturbation.anchoredPrimitive (2 * n)).eval z / (z - z0)‖ ≤
      ‖(Perturbation.perturbedPolynomial (basePolynomial g) n).eval z / (z - z0)‖ := by
    rw [hratio]
    simpa only [norm_neg, sub_neg_eq_add] using
      norm_sub_norm_le (g.eval z) (-((Perturbation.anchoredPrimitive (2 * n)).eval z / (z - z0)))
  rw [hp1]
  linarith [hAn.2]

/-- General final polynomial construction: the hypotheses are precisely the
three polynomial properties supplied by the approximation stage. -/
theorem exists_allBadWitness_of_base_polynomial (g : ℂ[X])
    (hg0 : g.eval z0 = 1)
    (hderiv : ∀ z ∈ K, (basePolynomial g).derivative.eval z ≠ 0)
    (hboundary : ∀ z : ℂ, ‖q.eval z‖ = 1 → 1 < ‖g.eval z‖) :
    ∃ P : ℂ[X], AllBadWitness P := by
  obtain ⟨n, hn⟩ := (eventually_allBadWitness_perturbation g hg0 hderiv hboundary).exists
  exact ⟨perturbationWitness g n, hn⟩

end
end SmaleConstruction

/- ## Counterexample construction: Model -/

namespace SmaleConstruction
open Polynomial Complex Set Metric

lemma blaschke_normSq_difference (r : ℝ) (w : ℂ) :
    Complex.normSq (w - (r : ℂ)) - Complex.normSq (1 - (r : ℂ) * w) =
      (1 - r ^ 2) * (Complex.normSq w - 1) := by
  simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im]
  ring

lemma norm_blaschke_lt_one {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {w : ℂ} (hw : ‖w‖ < 1) : ‖blaschke r w‖ < 1 := by
  have hd := blaschke_denom_ne_zero hr0 hr1 hw.le
  have hdiff := blaschke_normSq_difference r w
  rw [← Complex.sq_norm, ← Complex.sq_norm, ← Complex.sq_norm] at hdiff
  have hr : 0 < 1 - r ^ 2 := by nlinarith
  have hw2 : ‖w‖ ^ 2 < 1 := by nlinarith [norm_nonneg w]
  have hneg : (1 - r ^ 2) * (‖w‖ ^ 2 - 1) < 0 :=
    mul_neg_of_pos_of_neg hr (by linarith)
  have hn : ‖w - (r : ℂ)‖ < ‖1 - (r : ℂ) * w‖ := by
    exact (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by linarith)
  rw [blaschke, norm_div]
  exact (div_lt_iff₀ (norm_pos_iff.mpr hd)).mpr (by simpa using hn)

lemma norm_blaschke_eq_one {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {w : ℂ} (hw : ‖w‖ = 1) : ‖blaschke r w‖ = 1 := by
  have hd := blaschke_denom_ne_zero hr0 hr1 hw.le
  have hdiff := blaschke_normSq_difference r w
  rw [← Complex.sq_norm, ← Complex.sq_norm, ← Complex.sq_norm, hw] at hdiff
  have hn : ‖w - (r : ℂ)‖ = ‖1 - (r : ℂ) * w‖ := by
    nlinarith [norm_nonneg (w - (r : ℂ)), norm_nonneg (1 - (r : ℂ) * w)]
  rw [blaschke, norm_div, hn, div_self (norm_ne_zero_iff.mpr hd)]

lemma Jfun_at_base : Jfun (W z0) = 0 := by
  rw [Jfun_eq_mul_deriv_W norm_W_z0_lt_one.le, Phi_W z0_mem_K]
  simp

/-- A fully normalized holomorphic model with a zero-free derivative on the
whole quartic lemniscate and strictly expanding boundary quotients. -/
theorem exists_model :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ modelG r z0 = 1 ∧
      (∀ z ∈ K, deriv (modelF r) z ≠ 0) ∧
      (∀ z : ℂ, ‖q.eval z‖ = 1 → 1 < ‖modelG r z‖) := by
  obtain ⟨r, hr0, hr1, hM⟩ := disk_exclusion (J := Jfun) (a := 1 / 32)
    continuousOn_Jfun analyticAt_Jfun_one (by norm_num)
    (by rw [Jfun_one]; push_cast; ring) (by rw [deriv_Jfun_one]; norm_num)
  have hB : blaschke r (W z0) ≠ 0 := by
    intro hz
    have hd := blaschke_denom_ne_zero hr0.le hr1 norm_W_z0_lt_one.le
    have heq : W z0 = (r : ℂ) := by
      have : W z0 - (r : ℂ) = 0 := (div_eq_zero_iff.mp hz).resolve_right hd
      exact sub_eq_zero.mp this
    apply hM (W z0) norm_W_z0_lt_one.le
    rw [Jfun_at_base, heq]
    ring
  refine ⟨r, hr0, hr1, ?_, ?_, ?_⟩
  · simp [modelG, hB]
  · intro z hz
    have hw : ‖W z‖ ≤ 1 := by simpa using W_mem_closedBall hz
    have hd := blaschke_denom_ne_zero hr0.le hr1 hw
    have he := deriv_modelF_Phi_of_mem_closedBall hr0.le hr1 hw
    rw [Phi_W hz] at he
    rw [he]
    exact div_ne_zero (hM (W z) hw) (mul_ne_zero hB (pow_ne_zero 2 hd))
  · intro z hz
    have hw := norm_W_eq_one_of_q_norm_eq_one hz
    have hb := norm_blaschke_lt_one hr0.le hr1 norm_W_z0_lt_one
    rw [modelG, norm_div, norm_blaschke_eq_one hr0.le hr1 hw]
    exact (lt_div_iff₀ (norm_pos_iff.mpr hB)).mpr (by simpa using hb)

end SmaleConstruction

/- ## Counterexample construction: Complete -/

namespace SmaleConstruction
open Polynomial

theorem exists_allBadWitness : ∃ p : ℂ[X], AllBadWitness p := by
  obtain ⟨r, hr0, hr1, hnorm, hderiv, hboundary⟩ := exists_model
  obtain ⟨g, hg0, hgderiv, hgboundary⟩ :=
    exists_base_polynomial hr0 hr1 hnorm hderiv hboundary
  exact exists_allBadWitness_of_base_polynomial g hg0 hgderiv hgboundary

theorem weak_mean_value_false :
    ¬ (∀ (p : Polynomial ℂ), 2 ≤ p.degree → ∀ (z : ℂ) (_K : ℝ),
      ∃ c : ℂ, p.derivative.eval c = 0 ∧
        ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ ‖p.derivative.eval z‖) := by
  intro h
  obtain ⟨p, hpdeg, hpzero, hpderiv, hpbad⟩ := exists_allBadWitness
  obtain ⟨c, hc, hle⟩ := h p hpdeg 0 0
  have hle' : ‖p.eval c / c‖ ≤ 1 := by
    simpa [hpzero, hpderiv, norm_div] using hle
  exact (not_lt_of_ge hle') (hpbad c hc)


end SmaleConstruction

/--
**Disproof of Smale's mean value conjecture with constant 1** (the `mean_value_problem` statement of the
benchmark file): it is not the case that for every complex polynomial `p` of degree at least 2 and every
`z` some critical point `c` satisfies `‖p z - p c‖ / ‖z - c‖ ≤ ‖p' z‖`.
-/
theorem MeanValueProblem.mean_value_problem.disproof : ¬ (∀ (p : Polynomial ℂ), 2 ≤ p.degree → ∀ (z : ℂ) (K : ℝ),
    ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ ‖p.derivative.eval z‖) := by
  exact SmaleConstruction.weak_mean_value_false
