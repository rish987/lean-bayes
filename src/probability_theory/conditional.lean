import measure_theory.measure.measure_space
import probability_theory.independence

namespace ennreal

lemma inv_mul_eq_iff_eq_mul {x y z : ennreal} (hnz : z ≠ 0) (hnt : z ≠ ⊤) :
  x = z * y ↔ z ⁻¹ * x = y :=
by split; rintro rfl; simp [←mul_assoc, inv_mul_cancel, mul_inv_cancel, hnt, hnz]

lemma to_nnreal_ne_zero {a : ennreal} (hnz : a ≠ 0) (hnt : a ≠ ⊤) :
  a.to_nnreal ≠ 0 :=
begin
  intro haz,
  have : ↑(a.to_nnreal) = (0 : ennreal) := coe_eq_zero.mpr haz,
  rw coe_to_nnreal hnt at this,
  contradiction
end

lemma coe_to_nnreal_inv {a : ennreal} (hnz : a ≠ 0) (hnt : a ≠ ⊤) :
  ↑(a.to_nnreal)⁻¹ = a⁻¹ :=
begin
  convert coe_inv _,
    exact (coe_to_nnreal hnt).symm,
  exact to_nnreal_ne_zero hnz hnt
end

@[simp]
lemma ennreal.mul_inv {a b : ennreal} (ha : a ≠ 0) (hb : b ≠ 0) (hx : a ≠ ⊤) (hy : b ≠ ⊤) :
  (a * b)⁻¹ = a⁻¹ * b⁻¹ :=
begin
  rw [← coe_to_nnreal_inv (mul_ne_zero ha hb) (mul_ne_top hx hy),
    to_nnreal_mul, mul_inv₀, coe_mul,
    coe_to_nnreal_inv ha hx, coe_to_nnreal_inv hb hy],
end

end ennreal

noncomputable theory

open measure_theory measurable_space

namespace probability_theory

section

variables {α : Type*} [measurable_space α] (μ : measure α)

section definitions

include μ

/-- The conditional probability measure of measure `μ` on set `s` is `μ` restricted to `s` 
and scaled by the inverse of `μ s` (to make it a probability measure). -/
def cond_measure (s : set α) : measure α :=
  (μ s)⁻¹ • μ.restrict s

end definitions

localized "notation  μ `[` s `|` t `]` := cond_measure μ t s" in probability_theory
localized "notation  μ `[|` t`]` := cond_measure μ t" in probability_theory

/-- The conditional probability measure of any finite measure on any conditionable set
is a probability measure. -/
instance cond_prob_meas [is_finite_measure μ] {s : set α} (hcs : μ s ≠ 0) :
  is_probability_measure (μ[|s]) :=
  ⟨by rw [cond_measure, measure.smul_apply, measure.restrict_apply measurable_set.univ,
    set.univ_inter, ennreal.inv_mul_cancel hcs (measure_ne_top _ s)]⟩

variable [is_probability_measure μ]

section bayes

/-- The axiomatic definition of conditional probability derived from a measure-theoretic one. -/
@[simp] lemma cond_measure_def {a : set α} (hma : measurable_set a) (b : set α) :
  μ[b|a] = (μ a)⁻¹ * μ (a ∩ b) :=
by rw [cond_measure, measure.smul_apply, measure.restrict_apply' hma, set.inter_comm]

lemma cond_cond_meas_of_cond_meas_inter {s t : set α} (hms : measurable_set s)
  (hci : μ (s ∩ t) ≠ 0) : μ[|s] t ≠ 0 :=
begin
  rw cond_measure_def,
  refine mul_ne_zero _ _,
  exact ennreal.inv_ne_zero.mpr (measure_ne_top _ _),
  all_goals {assumption}
end

lemma cond_meas_inter_of_cond_cond_meas {s t : set α} (hms : measurable_set s)
  (hctcs : (μ[|s]) t ≠ 0) : μ (s ∩ t) ≠ 0 :=
begin
  refine (right_ne_zero_of_mul _),
  exact (μ s)⁻¹,
  convert hctcs,
  change μ (s ∩ t) = (μ.restrict s) t,
  rw [measure.restrict_apply' hms, set.inter_comm]
end

lemma meas_subset_ne {a b : set α} (hs : a ⊆ b) (hnz : μ a ≠ 0) : μ b ≠ 0 :=
  pos_iff_ne_zero.mp (gt_of_ge_of_gt (μ.mono hs) (pos_iff_ne_zero.mpr hnz))

/-- Conditioning first on `a` and then on `b` results in the same measure as conditioning
on `a ∩ b`. -/
@[simp] lemma cond_cond_eq_cond_inter {a : set α} {b : set α} (hma : measurable_set a) (hmb : measurable_set b) (hca : μ a ≠ 0)
  (hci : μ (a ∩ b) ≠ 0) :
  μ[|a][|b] = (μ[|(a ∩ b)]) :=
begin
  apply measure.ext,
  intros s hms,
  haveI := probability_theory.cond_prob_meas μ (meas_subset_ne μ (set.inter_subset_left _ _) hci),
  simp [*, measure_ne_top],
  conv { to_lhs, rw mul_assoc, congr, skip, rw mul_comm },
  simp_rw ← mul_assoc,
  rw [ennreal.mul_inv_cancel hca (measure_ne_top _ a), one_mul,
    ← set.inter_assoc, mul_comm]
end

@[simp] lemma cond_inter {a : set α} (hma : measurable_set a) (hca : μ a ≠ 0) (b : set α) :
  μ[b|a] * μ a = μ (a ∩ b) :=
by rw [cond_measure_def μ hma b, mul_comm, ←mul_assoc,
  ennreal.mul_inv_cancel hca (measure_ne_top _ a), one_mul]

/-- Bayes' Theorem. -/
theorem bayes (a : set α) (hma : measurable_set a)
  (b : set α) (hmb : measurable_set b) (hcb : μ b ≠ 0) :
  μ[b|a] = (μ a)⁻¹ * μ[a|b] * (μ b) :=
by rw [mul_assoc, cond_inter μ hmb hcb a, set.inter_comm, cond_measure_def _ hma]; apply_instance

section indep

/-- Two measurable sets are independent if and only if conditioning on one
is irrelevant to the probability of the other. -/
theorem indep_set_iff_cond_irrel {a : set α} (hma : measurable_set a)
  {b : set α} (hmb : measurable_set b) :
  indep_set a b μ ↔ μ a ≠ 0 → μ[b|a] = μ b :=
begin
  split; intro h,
    intro hca, 
    rw [cond_measure_def _ hma, (indep_set_iff_measure_inter_eq_mul hma hmb μ).mp h,
      ← mul_assoc, ennreal.inv_mul_cancel hca (measure_ne_top _ _), one_mul], apply_instance,
  by_cases hca : μ a = 0,
  { rw indep_set_iff_measure_inter_eq_mul hma hmb μ,
    simp [measure_inter_null_of_null_left, hca] },
  { have hcond := h hca,
    refine (indep_set_iff_measure_inter_eq_mul hma hmb μ).mpr _,
    rwa [ ennreal.inv_mul_eq_iff_eq_mul hca (measure_ne_top _ _), set.inter_comm,
      ← measure.restrict_apply' hma] },
end

lemma symm_iff {α} {s₁ s₂ : set (set α)} [measurable_space α] {μ : measure α} :
  indep_sets s₁ s₂ μ ↔ indep_sets s₂ s₁ μ :=
⟨indep_sets.symm, indep_sets.symm⟩

theorem indep_set_iff_cond_irrel' (a : set α) (hma : measurable_set a) (b : set α) (hmb : measurable_set b) :
  indep_set b a μ ↔ μ a ≠ 0 → μ[b|a] = μ b :=
iff.trans symm_iff (indep_set_iff_cond_irrel _ hma hmb)

def cond_Indep_sets {α ι} [measurable_space α] (π : ι → set (set α))
  (C : set (set α)) (μ : measure α . volume_tac) : Prop :=
∀ (c ∈ C), Indep_sets π (μ[|c])

def cond_indep_sets {α} [measurable_space α] (s1 s2 : set (set α)) (C : set (set α))
  (μ : measure α . volume_tac) : Prop :=
∀ (c ∈ C), indep_sets s1 s2 (μ[|c])

def cond_Indep {α ι} (m : ι → measurable_space α) [measurable_space α] (C : set (set α))
  (μ : measure α . volume_tac) : Prop :=
cond_Indep_sets (λ x, (m x).measurable_set') C μ 

lemma cond_Indep_def {α ι} (m : ι → measurable_space α) [measurable_space α]
  (C : set (set α)) (μ : measure α . volume_tac) :
  cond_Indep m C μ = ∀ c ∈ C, Indep m (μ[|c]) := rfl

def cond_indep {α} (m₁ m₂ : measurable_space α) [measurable_space α] (C : set (set α))
  (μ : measure α . volume_tac) : Prop :=
cond_indep_sets (m₁.measurable_set') (m₂.measurable_set') C μ

lemma cond_indep_def {α} (m₁ m₂ : measurable_space α) [measurable_space α] (C : set (set α))
  (μ : measure α . volume_tac) :
  cond_indep m₁ m₂ C μ = ∀ c ∈ C, indep m₁ m₂ (μ[|c]) := rfl

def cond_Indep_set {α ι} [measurable_space α] (s : ι → set α) (C : set (set α))
  (μ : measure α . volume_tac) : Prop :=
cond_Indep (λ i, generate_from {s i}) C μ

lemma cond_Indep_set_def {α ι} [measurable_space α] (s : ι → set α) (C : set (set α))
  (μ : measure α . volume_tac) : cond_Indep_set s C μ = ∀ c ∈ C, Indep_set s (μ[|c]) := rfl

def cond_indep_set {α} [measurable_space α] (s t : set α) (C : set (set α))
  (μ : measure α . volume_tac) : Prop :=
cond_indep (generate_from {s}) (generate_from {t}) C μ

def cond_indep_set' {α} [measurable_space α] (s t : set α) (c : set α)
  (μ : measure α . volume_tac) : Prop :=
cond_indep_set s t {c} μ

lemma cond_indep_set'.symm {α} {s t c : set α} [measurable_space α] {μ : measure α}
  (h : cond_indep_set' s t c μ) : cond_indep_set' t s c μ :=
by { intros c hc a b ha hb, rw [set.inter_comm, mul_comm], exact h c hc b a hb ha }

lemma cond_indep_set'.symm_iff {α} {s t c : set α} [measurable_space α] {μ : measure α} :
  cond_indep_set' s t c μ ↔ cond_indep_set' t s c μ :=
⟨cond_indep_set'.symm, cond_indep_set'.symm⟩

def cond_indep_set_def {α} [measurable_space α] (s t : set α) (C : set (set α))
  (μ : measure α . volume_tac) :
  cond_indep_set s t C μ = ∀ c ∈ C, indep_set s t (μ[|c]) := rfl

def cond_indep_set_def' {α} [measurable_space α] (s t : set α) (c : set α)
  (μ : measure α . volume_tac) :
  cond_indep_set' s t c μ = indep_set s t (μ[|c]) :=
by have : cond_indep_set' s t c μ = ∀ (x ∈ {x | x = c}), indep_set s t (μ[|x]) := rfl;
  simp [this]

def cond_Indep_fun {α ι} [measurable_space α] {β : ι → Type*}
  (m : Π (x : ι), measurable_space (β x))
  (f : Π (x : ι), α → β x) (C : set (set α)) (μ : measure α . volume_tac) : Prop :=
cond_Indep (λ x, measurable_space.comap (f x) (m x)) C μ

def cond_Indep_fun_def {α ι} [measurable_space α] {β : ι → Type*}
  (m : Π (x : ι), measurable_space (β x))
  (f : Π (x : ι), α → β x) (C : set (set α)) (μ : measure α . volume_tac) :
  cond_Indep_fun m f C μ = ∀ c ∈ C, Indep_fun m f (μ[|c]) := rfl

def cond_indep_fun {α β γ} [measurable_space α] [mβ : measurable_space β]
  [mγ : measurable_space γ]
  (f : α → β) (g : α → γ) (C : set (set α)) (μ : measure α . volume_tac) : Prop :=
cond_indep (measurable_space.comap f mβ) (measurable_space.comap g mγ) C μ

def cond_indep_fun_def {α ι} [measurable_space α] {β : ι → Type*}
  (m : Π (x : ι), measurable_space (β x))
  (f : Π (x : ι), α → β x) (C : set (set α)) (μ : measure α . volume_tac) :
  cond_Indep_fun m f C μ = ∀ c ∈ C, Indep_fun m f (μ[|c]) := rfl

theorem cond_meas_inter (a : set α) {b : set α} (hmb : measurable_set b) :
  μ (b ∩ a) ≠ 0 ↔ (μ[|b] a ≠ 0) :=
begin
  split; intro hc,
    simp [*, measure_ne_top],
  simp [*, not_or_distrib] at hc,
  exact hc.2
end

def indep_set_of_cond_null_measure (a b c : set α) (hmc : measurable_set c) (h : μ c = 0) : indep_set a b (μ [| c]) :=
by rw [indep_set, indep, indep_sets]; intros; simp [hmc, h, measure_inter_null_of_null_left]

def indep_sets_of_cond_null_measure (a b : set (set α)) (c : set α) (hmc : measurable_set c) (h : μ c = 0) : indep_sets a b (μ [| c]) :=
by intros _ _ _ _; simp [hmc, h, measure_inter_null_of_null_left]

def cond_indep_set_iff_cond_inter_irrel {a : set α} (hma : measurable_set a)
  {b : set α} (hmb : measurable_set b) {c : set α} (hmc : measurable_set c) :
  cond_indep_set' a b c μ ↔ μ (c ∩ a) ≠ 0 → μ[b|c ∩ a] = μ[b|c] :=
begin
  by_cases h : μ c = 0,
  { rw [cond_indep_set_def'],
    refine iff_of_true (indep_set_of_cond_null_measure _ _ _ _ hmc h) _,
    { refine not.elim _,
      intro,
      have := measure_inter_null_of_null_left a h,
      contradiction } },
  { have : μ (c ∩ a) ≠ 0 → (μ[b|c ∩ a] = μ[b|c] ↔ (μ[|c][|a]) b = μ[b|c]),
    { intro h, haveI := h,
      rw ← cond_cond_eq_cond_inter μ hmc hma _ h,
      exact (meas_subset_ne _ (set.inter_subset_left _ _) h) },
    haveI := probability_theory.cond_prob_meas μ h,
    rw [cond_indep_set_def', forall_congr this, cond_meas_inter, indep_set_iff_cond_irrel];
    assumption }
end

theorem cond_indep_set_iff_cond_inter_irrel' {a : set α} (hma : measurable_set a)
  {b : set α} (hmb : measurable_set b) {c : set α} (hmc : measurable_set c)
  : cond_indep_set' b a c μ ↔ μ (c ∩ a) ≠ 0 → μ[b|c ∩ a] = μ[b|c] :=
iff.trans cond_indep_set'.symm_iff (cond_indep_set_iff_cond_inter_irrel _ hma hmb hmc)

end indep

end bayes

end

end probability_theory
