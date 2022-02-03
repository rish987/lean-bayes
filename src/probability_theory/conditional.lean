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

/-- Type class wrapper for measurable sets. -/
class meas (s : set α) : Prop :=
(meas : measurable_set s)

/-- Type class wrapper for measurable functions. -/
class fmeas [measurable_space α] {β : Type*} [measurable_space β] (f : α → β) : Prop :=
(fmeas : measurable f)

include μ

/-- Represents the notion that a conditional probability measure "exists" for a measure `μ`
and set `s` exactly when `s` is measurable with nonzero measure. -/
class cond_meas (s : set α) extends meas s : Prop :=
(meas_nz : μ s ≠ 0)

/-- The conditional probability measure of measure `μ` on set `s` is `μ` restricted to `s` 
and scaled by the inverse of `μ s` (to make it a probability measure). -/
def cond_measure (s : set α) : measure α :=
  (μ s)⁻¹ • μ.restrict s

end definitions

-- TODO can this theorem be inferred automatically somehow?
lemma cond_meas_iff (s : set α) : cond_meas μ s ↔ μ s ≠ 0 ∧ measurable_set s :=
begin
  split,
    intro hcms,
    exact ⟨hcms.meas_nz, hcms.meas⟩,
  rintro ⟨hnz, hm⟩,
  haveI := meas.mk hm,
  exact ⟨hnz⟩
end

localized "notation  μ `[` s `|` t `]` := cond_measure μ t s" in probability_theory
localized "notation  μ `[|` t`]` := cond_measure μ t" in probability_theory

/-- The conditional probability measure of any finite measure on any conditionable set
is a probability measure. -/
instance [is_finite_measure μ] {s : set α} [hcms : cond_meas μ s] :
  is_probability_measure (μ[|s]) :=
  ⟨by rw [cond_measure, measure.smul_apply, measure.restrict_apply measurable_set.univ,
    set.univ_inter, ennreal.inv_mul_cancel hcms.meas_nz (measure_ne_top _ s)]⟩

variable [is_probability_measure μ] 

section bayes

/-- The axiomatic definition of conditional probability derived from a measure-theoretic one. -/
@[simp] lemma cond_measure_def (a : set α) [hma : meas a] (b : set α) :
  μ[b|a] = (μ a)⁻¹ * μ (a ∩ b) :=
by rw [cond_measure, measure.smul_apply, measure.restrict_apply' hma.meas, set.inter_comm]

instance meas_inter_of_meas [measurable_space α] {s t : set α} [h1 : meas s] [h2 : meas t] :
  meas (s ∩ t) := ⟨measurable_set.inter h1.meas h2.meas⟩

-- TODO can I replace the below two instances with something like this?
--instance cond_meas_of_cond_meas_subset {s t : set α} [meas t]
--  [hcmi : cond_meas μ s] [hsub : inhabited (s ⊆ t)] :
--  cond_meas μ t := ⟨ne_bot_of_le_ne_bot hcmi.meas_nz (μ.mono hsub.default)⟩

instance cond_meas_of_cond_meas_inter₀ {s t : set α} [meas t] [hcmi : cond_meas μ (s ∩ t)] :
  cond_meas μ t := ⟨ne_bot_of_le_ne_bot hcmi.meas_nz (μ.mono (set.inter_subset_right _ _))⟩

instance cond_meas_of_cond_meas_inter₁ {s t : set α} [meas s] [hcmi : cond_meas μ (s ∩ t)] :
  cond_meas μ s := ⟨ne_bot_of_le_ne_bot hcmi.meas_nz (μ.mono (set.inter_subset_left _ _))⟩

instance cond_cond_meas_of_cond_meas_inter {s t : set α} [cond_meas μ s]
  [meas t] [hcmi : cond_meas μ (s ∩ t)] :
  cond_meas (μ[|s]) t :=
begin
  constructor,
  rw cond_measure_def,
  refine mul_ne_zero _ _,
  exact ennreal.inv_ne_zero.mpr (measure_ne_top _ _),
  exact hcmi.meas_nz
end

instance cond_meas_inter_of_cond_cond_meas {s t : set α} [hmcs : cond_meas μ s]
  [hmcc : cond_meas (μ[|s]) t] :
  cond_meas μ (s ∩ t) :=
begin
  haveI : meas (s ∩ t) := ⟨measurable_set.inter hmcs.meas hmcc.meas⟩,
  constructor,
  refine (right_ne_zero_of_mul _),
  exact (μ s)⁻¹,
  convert hmcc.meas_nz,
  change μ (s ∩ t) = (μ.restrict s) t,
  rw [measure.restrict_apply' hmcs.meas, set.inter_comm]
end

/-- Conditioning first on `a` and then on `b` results in the same measure as conditioning
on `a ∩ b`. -/
@[simp] lemma cond_cond_eq_cond_inter (a : set α) (b : set α) [hcma : cond_meas μ a]
  [cond_meas (μ[|a]) b] [hcmr : cond_meas μ (a ∩ b)] :
  μ[|a][|b] = (μ[|(a ∩ b)]) :=
begin
  apply measure.ext,
  intros s hms,
  simp [hcma.meas_nz, hcmr.meas_nz, measure_ne_top],
  conv { to_lhs, rw mul_assoc, congr, skip, rw mul_comm },
  simp_rw ← mul_assoc,
  rw [ennreal.mul_inv_cancel hcma.meas_nz (measure_ne_top _ a), one_mul,
    ← set.inter_assoc, mul_comm]
end

@[simp] lemma cond_inter (a : set α) [hcma : cond_meas μ a] (b : set α) :
  μ[b|a] * μ a = μ (a ∩ b) :=
by rw [cond_measure_def μ a b, mul_comm, ←mul_assoc,
  ennreal.mul_inv_cancel hcma.meas_nz (measure_ne_top _ a), one_mul]

/-- Bayes' Theorem. -/
theorem bayes (a : set α) [cond_meas μ a] (b : set α) [cond_meas μ b] :
  μ[b|a] = (μ a)⁻¹ * μ[a|b] * (μ b) :=
by rw [mul_assoc, cond_inter μ b a, set.inter_comm, cond_measure_def]

section indep

/-- Two measurable sets are independent if and only if conditioning on one
is irrelevant to the probability of the other. -/
theorem indep_set_iff_cond_irrel (a : set α) [hma : meas a] (b : set α) [hmb : meas b] :
  indep_set a b μ ↔ cond_meas μ a → μ[b|a] = μ b :=
begin
  split,
    intros hind hcma, 
    haveI := hcma,
    rw [cond_measure_def, (indep_set_iff_measure_inter_eq_mul hma.meas hmb.meas μ).mp hind,
      ← mul_assoc, ennreal.inv_mul_cancel hcma.meas_nz (measure_ne_top _ _), one_mul],
  intro hcondi, 
  by_cases hcma : cond_meas μ a,
  { have hcond := hcondi hcma,
    refine (indep_set_iff_measure_inter_eq_mul hma.meas hmb.meas μ).mpr _,
    rwa [ ennreal.inv_mul_eq_iff_eq_mul hcma.meas_nz (measure_ne_top _ _), set.inter_comm,
      ← measure.restrict_apply' hma.meas] },
  { have hz : μ a = 0,
    {  simp [cond_meas_iff] at hcma,
       exact not_imp_not.mp hcma hma.meas },
    rw indep_set_iff_measure_inter_eq_mul hma.meas hmb.meas μ,
    simp [measure_inter_null_of_null_left, hz] }
end

lemma symm_iff {α} {s₁ s₂ : set (set α)} [measurable_space α] {μ : measure α} :
  indep_sets s₁ s₂ μ ↔ indep_sets s₂ s₁ μ :=
⟨indep_sets.symm, indep_sets.symm⟩

theorem indep_set_iff_cond_irrel' (a : set α) [meas a] (b : set α) [meas b] :
  indep_set b a μ ↔ cond_meas μ a → μ[b|a] = μ b :=
iff.trans symm_iff (indep_set_iff_cond_irrel _ _ _)

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
  (h : cond_indep_set' s t c μ) : cond_indep_set' t s c μ := sorry

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

theorem cond_meas_inter (a : set α) [meas a] (b : set α) [meas b]
  : cond_meas μ (b ∩ a) ↔ cond_meas (μ[|b]) a :=
begin
  split; intro hcm; constructor,
    rw cond_measure_def,
    simp [hcm.meas_nz, measure_ne_top],
  have := hcm.meas_nz,
  simp [cond_measure_def, not_or_distrib] at this,
  exact this.2
end

def cond_indep_set_iff_cond_inter_irrel (a : set α) [hma : meas a]
  (b : set α) [hmb : meas b]
  (c : set α) [hmc : meas c] :
  cond_indep_set' a b c μ ↔ cond_meas μ (c ∩ a) → μ[b|c ∩ a] = μ[b|c] :=
begin
  have : cond_meas μ (c ∩ a) → (μ[b|c ∩ a] = μ[b|c] ↔ (μ[|c][|a]) b = μ[b|c]),
  { intro h, haveI := h, rw ← cond_cond_eq_cond_inter },
  by_cases h : cond_meas μ c,
    haveI := h,
    rw [cond_indep_set_def', forall_congr this, cond_meas_inter, indep_set_iff_cond_irrel],
  have hz : μ c = 0,
  -- TODO make a lemma for this
  {  simp [cond_meas_iff] at h,
       exact not_imp_not.mp h hmc.meas },
  have inter_z : ∀ x, μ (c ∩ x) = 0 := sorry,
  rw [cond_indep_set_def', indep_set, indep, indep_sets],
  refine iff_of_true _ _,
  { intros s t hgs hgt,
    simp_rw cond_measure_def,
    simp [inter_z] },
  { refine not.elim _,
    simp [cond_meas_iff],
    intro,
    have := inter_z a,
    contradiction }
end

theorem cond_indep_set_iff_cond_inter_irrel' (a : set α) [meas a]
  (b : set α) [meas b]
  (c : set α) [meas c]
  : cond_indep_set' b a c μ ↔ cond_meas μ (c ∩ a) → μ[b|c ∩ a] = μ[b|c] :=
iff.trans cond_indep_set'.symm_iff (cond_indep_set_iff_cond_inter_irrel _ _ _ _)

end indep

end bayes

end

end probability_theory
