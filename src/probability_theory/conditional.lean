import measure_theory.measure.measure_space
import probability_theory.independence

noncomputable theory

open measure_theory measurable_space

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

namespace probability_theory

section

variables {α : Type*} [m : measurable_space α] (μ : measure α)

section definitions

class measurable (s : set α) : Prop :=
(meas : m.measurable_set' s)

include μ

class cond_measurable (s : set α) extends measurable s :=
(meas_nz : μ s ≠ 0)

def cond_measure (s : set α) : measure α :=
  (μ s)⁻¹ • μ.restrict s

end definitions

variable [is_probability_measure μ] 

instance {s : set α} [hcms : cond_measurable μ s] : is_probability_measure (cond_measure μ s) :=
  ⟨by rw [cond_measure, measure.smul_apply, measure.restrict_apply measurable_set.univ,
    set.univ_inter, ennreal.inv_mul_cancel hcms.meas_nz (measure_ne_top _ s)]⟩

section bayes

variables (a : set α)

@[simp]
lemma cond_def [hma : measurable a] (b : set α) :
  cond_measure μ a b = (μ a)⁻¹ * μ (a ∩ b) :=
  by rw [cond_measure, measure.smul_apply, measure.restrict_apply' hma.meas, set.inter_comm]

instance cond_cond_meas_of_cond_meas_inter {s t : set α} [hmcs : cond_measurable μ s]
  [hmt : measurable t] [hcmi : cond_measurable μ (s ∩ t)] :
  cond_measurable (cond_measure μ s) t :=
begin
  constructor,
  rw cond_def,
  refine mul_ne_zero _ _,
  exact ennreal.inv_ne_zero.mpr (measure_ne_top _ _),
  exact hcmi.meas_nz
end

instance cond_meas_inter_of_cond_cond_meas {s t : set α} [hmcs : cond_measurable μ s]
  [hmcc : cond_measurable (cond_measure μ s) t] :
  cond_measurable μ (s ∩ t) :=
begin
  haveI : measurable (s ∩ t) := ⟨measurable_set.inter hmcs.meas hmcc.meas⟩,
  constructor,
  refine (right_ne_zero_of_mul _),
  exact (μ s)⁻¹,
  convert hmcc.meas_nz,
  change μ (s ∩ t) = (μ.restrict s) t,
  rw [measure.restrict_apply' hmcs.meas, set.inter_comm]
end

lemma cond_cond_def (b : set α) [hcma : cond_measurable μ a]
  [hcml : cond_measurable (cond_measure μ a) b] [hcmr : cond_measurable μ (a ∩ b)] :
  cond_measure (cond_measure μ a) b = cond_measure μ (a ∩ b) :=
begin
  apply measure.ext,
  intros s hms,
  simp [hcma.meas_nz, hcmr.meas_nz, measure_ne_top],
  conv { to_lhs, rw mul_assoc, congr, skip, rw mul_comm },
  simp_rw ← mul_assoc,
  rw [ennreal.mul_inv_cancel hcma.meas_nz (measure_ne_top _ a), one_mul,
    ← set.inter_assoc, mul_comm]
end

@[simp]
lemma cond_inter [hcma : cond_measurable μ a] (b : set α) :
  cond_measure μ a b * (μ a) = μ (a ∩ b) :=
by rw [cond_def μ a b, mul_comm, ←mul_assoc,
  ennreal.mul_inv_cancel hcma.meas_nz (measure_ne_top _ a), one_mul]

theorem bayes [hcma : cond_measurable μ a] {b : set α} [hcmb : cond_measurable μ b] :
  cond_measure μ a b * (μ a) = cond_measure μ b a * (μ b) :=
  by rw [cond_inter μ a b, cond_inter μ b a, set.inter_comm]

section indep

theorem indep_iff [hcma : cond_measurable μ a] (b : set α) [hmb : measurable b] :
  indep_set a b μ ↔ cond_measure μ a b = μ b :=
begin
  split,
    intro hind, 
    rw [cond_def μ a b, (indep_set_iff_measure_inter_eq_mul hcma.meas hmb.meas μ).mp hind,
      ← mul_assoc, ennreal.inv_mul_cancel hcma.meas_nz (measure_ne_top _ a), one_mul],
  intro hcond, 
  refine (indep_set_iff_indep_sets_singleton hcma.meas hmb.meas μ).mpr _,
  intros a' b' ha' hb',
  rwa [set.mem_singleton_iff.mp ha', set.mem_singleton_iff.mp hb',
    ennreal.inv_mul_eq_iff_eq_mul hcma.meas_nz (measure_ne_top _ a), set.inter_comm,
    ← measure.restrict_apply hmb.meas]
end

end indep

end bayes

end

end probability_theory
